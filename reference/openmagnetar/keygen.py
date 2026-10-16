"""KeyGen (docs/spec/11-protocol.md section 11.2): verifying/proving key derivation.

The verifying key is the *program-specific* key: ABI parameters, the code image, the data image, the
PCS profile.  Everything else (ROM, s_1, s_2, layout, R_sh, R_st, component list, Mosaic layout) is a
deterministic function of it and of the trace length T, and is derived here (`Derived`).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import cached_property

from . import abi, bytecode as bc, cpu_circuit as cpu, ligerito as lg, router
from . import twist as tw
from .field import K
from .hashing import Hasher
from .mosaic import Layout, compute_layout
from .r1cs import R1CS, SparseMatrix
from . import spartan

VK_VERSION = 1
MAX_LOG_T = 40
LOG_CYCLES = 2            # c = 2 cycles per SIMD instance (spec 10.2)
REG_A, REG_D, REG_P = 6, 2, 2
WORD_BITS = 6


class KeyError_(ValueError):
    pass


def choose_ad(a: int) -> tuple[int, int]:
    """(a, d): smallest d | a with a/d <= 4; if that gives a/d = 1 (and a > 1) a is padded up to a
    multiple of 4 and the rule is applied again (spec 07.9)."""
    def smallest(a):
        for d in range(1, a + 1):
            if a % d == 0 and a // d <= 4:
                return d
    d = smallest(a)
    if a > 1 and a // d == 1:
        a = -(-a // 4) * 4
        d = smallest(a)
    return a, d


@dataclass
class VerifyingKey:
    abi: abi.Params
    code: dict
    entry_pc: int
    m0_program: dict
    pcs: str = "ligerito"             # "ligerito" | "transparent" (test-only mock)
    pcs_profile: str = "provable-120"  # "provable-120" | "test"
    pcs_r: int = 2
    pcs_t: int = 0                    # queries per level when pcs_profile == "test"
    program_digest: bytes = b""

    def __post_init__(self):
        self.abi.validate()
        if self.pcs not in ("ligerito", "transparent") or self.pcs_profile not in ("provable-120", "test"):
            raise KeyError_("unknown pcs mode or profile")
        if self.pcs_profile == "provable-120":
            if not (2 <= self.pcs_r <= 8):
                raise KeyError_("provable-120 requires 2 <= pcs_r <= 8")
        else:
            if self.pcs_t < 1:
                raise KeyError_("test profile needs pcs_t >= 1")
            if not (1 <= self.pcs_r <= 8) or self.pcs_t > 256:
                raise KeyError_("bad test-profile pcs fields")
        if not self.program_digest:
            self.program_digest = abi.program_digest(self.code, self.entry_pc, self.m0_program, self.abi)
        elif self.program_digest != abi.program_digest(self.code, self.entry_pc, self.m0_program, self.abi):
            raise KeyError_("program digest mismatch")
        if len(self.code) > self.abi.max_code_words or self.entry_pc not in self.code:
            raise KeyError_("bad code image")

    @cached_property
    def hasher(self) -> Hasher:
        return Hasher(self.abi.hash_profile)

    def digest(self) -> bytes:
        from . import proof_format as pf
        return self.hasher.digest(b"openmagnetar/vk/v1" + pf.encode_vk(self))

    @cached_property
    def derived(self) -> "Derived":
        return Derived(self)


def keygen(code: dict, entry_pc: int, m0_program: dict | None = None, abi_params: abi.Params | None = None,
           pcs: str = "ligerito", pcs_profile: str = "provable-120", pcs_r: int = 2, pcs_t: int = 0
           ) -> VerifyingKey:
    """KeyGen: (code image, entry pc, data image, parameters) -> vk.  vk.derived holds the rest."""
    return VerifyingKey(abi_params or abi.Params(), dict(code), entry_pc, dict(m0_program or {}),
                        pcs, pcs_profile, pcs_r, pcs_t)


def keygen_from_elf(elf: bytes, abi_params: abi.Params, **kw) -> VerifyingKey:
    from . import elf as elfmod
    code, entry, m0 = elfmod.load(elf, abi_params)
    return keygen(code, entry, m0, abi_params, **kw)


def _matrix(rows: list, rho: int, nu: int, field_: str) -> SparseMatrix:
    return SparseMatrix(rho, nu, {(r, c): K(v) for r, row in enumerate(rows) for c, v in row.items()})


@dataclass
class Instance:
    """Parameters that depend on T (spec 11.3)."""
    T: int
    n: int
    s: int
    reg: tw.TwistParams
    ram: tw.TwistParams
    comps: list                 # [(name, log_size)] committed components in id order (after segments)
    ids: dict                   # component name -> id
    layout: Layout
    ell: int


class Derived:
    def __init__(self, vk: VerifyingKey):
        self.vk = vk
        self.cpu_params = cpu.Params(ram_log_words=vk.abi.ram_log_words, log_cycles=LOG_CYCLES)
        self.program = bc.expand(vk.code, vk.entry_pc)
        self.rom = self.program.rom
        self.N = len(self.rom)
        self.rom_a, self.rom_d = choose_ad(max(2, (self.N - 1).bit_length()))
        self.ram_a, self.ram_d = choose_ad(vk.abi.ram_log_words)
        self.segments = cpu.layout(self.cpu_params)
        self.seg_names = [sg.name for sg in self.segments]
        self.seg_id = {sg.name: i for i, sg in enumerate(self.segments)}
        s1, s2 = cpu.build_s1(self.cpu_params), cpu.build_s2(self.cpu_params)
        self.nu = (2 * cpu.num_w_cols(self.cpu_params)).bit_length() - 1
        self.rho = (max(len(s1), len(s2)) - 1).bit_length()
        self.rels = [R1CS("B", self.rho, self.nu, *[_matrix(M, self.rho, self.nu, "B") for M in (s1.A, s1.B, s1.C)]),
                     R1CS("K", self.rho, self.nu, *[_matrix(M, self.rho, self.nu, "K") for M in (s2.A, s2.B, s2.C)])]
        self.spartan_segments = [spartan.Segment(i, sg.kind, sg.log_size, sg.offset >> sg.log_size)
                                 for i, sg in enumerate(self.segments)]
        self.R_sh = router.shift_entries(WORD_BITS)
        self.R_st = router.store_entries(WORD_BITS)
        self.mm = abi.memory_map(vk.abi)
        self.rom_fields = [cpu._rom_fields(r) for r in self.rom]

    # ------------------------------------------------------------ per-T derivation
    def instance(self, T: int) -> Instance:
        if T < 4 or T & (T - 1) or T > 1 << MAX_LOG_T:
            raise KeyError_("T must be a power of two in [4, 2^%d]" % MAX_LOG_T)
        n = T.bit_length() - 1
        s = n - LOG_CYCLES
        reg = tw.TwistParams("twist/reg", REG_A, REG_D, REG_P, n, WORD_BITS)
        ram = tw.TwistParams("twist/ram", self.ram_a, self.ram_d, 1, n, WORD_BITS)
        comps = []
        for x in ("ra0", "ra1", "wa"):
            for i in range(REG_D):
                comps.append((f"twist/reg/{x}/{i + 1}", REG_A // REG_D + n))
        comps.append(("twist/reg/inc", WORD_BITS + n))
        for i in range(self.ram_d):
            comps.append((f"twist/ram/ra0/{i + 1}", self.ram_a // self.ram_d + n))
        comps.append(("twist/ram/inc", WORD_BITS + n))
        for i in range(self.rom_d):
            comps.append((f"shout/bytecode/ra/{i + 1}", self.rom_a // self.rom_d + n))
        ids = {sg.name: i for i, sg in enumerate(self.segments)}
        nid = len(self.segments)
        for nm, _ in comps:
            ids[nm] = nid
            nid += 1
        for i in range(self.ram_d):     # RAM write address = read address (07.9)
            ids[f"twist/ram/wa/{i + 1}"] = ids[f"twist/ram/ra0/{i + 1}"]
        allc = [(i, sg.log_size + s)
                for i, sg in enumerate(self.segments) if sg.kind == "direct"]
        allc += [(ids[nm], ls) for nm, ls in comps]
        layout = compute_layout(allc, 8 if self.vk.pcs == "ligerito" else 0)
        return Instance(T, n, s, reg, ram, comps, ids, layout, layout.ell)

    def ligerito_params(self, ell: int) -> lg.LigeritoParams:
        from . import params as parmod
        vk = self.vk
        n = ell - 7
        if n < 2:
            raise KeyError_("G too small for ring switching + Ligerito")
        if vk.pcs_profile == "provable-120":
            try:
                p = lg.make_params(n, "provable-120", vk.pcs_r)
            except ValueError as e:
                raise KeyError_(str(e)) from e
            log_t = max(2, min(MAX_LOG_T, ell - parmod.ELL_OFFSET))
            m = parmod.Machine(
                log_t=log_t, c=LOG_CYCLES, rho=self.rho, nu=self.nu, lam=8,
                reg_a=REG_A, reg_d=REG_D, reg_p=REG_P,
                ram_a=self.ram_a, ram_d=self.ram_d,
                out_m=vk.abi.output_log_words,
                rom_a=self.rom_a, rom_d=self.rom_d, rom_groups=3,
                mosaic_claims=128, ell_offset=max(0, ell - log_t),
            )
            L = parmod.ledger(log_t, "provable-120", machine=m, params=p)
            if not L.provable or L.min_rbr_bits < parmod.TARGET:
                raise KeyError_(f"provable-120 soundness ledger violated: {L.min_rbr_bits:.3f} < {parmod.TARGET}")
            return p
        final = min(6, n - 1)
        ks = lg.schedule(n, final=final)
        return lg.LigeritoParams(n, tuple(ks), (vk.pcs_r,) * len(ks), (vk.pcs_t,) * len(ks))
