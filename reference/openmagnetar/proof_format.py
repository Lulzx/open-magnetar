"""Canonical byte encodings of the verifying key, public instance and proof (docs/spec/12-proof-format.md).

All integers are little-endian; K elements are the 16-byte encodings of C1.  Lengths that follow from
(vk, T) are *not* transmitted; the only length prefixes are the u32 counts inside Ligerito openings.
Parsers reject short input, trailing bytes and any structure that does not match the expected shape.
"""

from __future__ import annotations

import struct

from . import abi, ligerito as lg, ring_switch as rsw, router as rt, spartan, twist as tw
from .field import K
from .keygen import REG_A, VerifyingKey, VK_VERSION
from .mosaic import BatchProof
from .onehot import OneHotProof, VirtProof
from .shout import ShoutProof
from .sumcheck import SumcheckProof

MAGIC_VK, MAGIC_INSTANCE, MAGIC_PROOF = b"OMVK", b"OMIN", b"OMPF"
PROOF_VERSION = 1
MAX_BYTES = 1 << 40


class FormatError(ValueError):
    pass


class Reader:
    def __init__(self, data: bytes):
        self.d, self.p = data, 0

    def take(self, n: int) -> bytes:
        if n < 0 or self.p + n > len(self.d):
            raise FormatError("truncated input")
        b = self.d[self.p:self.p + n]
        self.p += n
        return b

    def u8(self) -> int:
        return self.take(1)[0]

    def u32(self) -> int:
        return struct.unpack("<I", self.take(4))[0]

    def u64(self) -> int:
        return struct.unpack("<Q", self.take(8))[0]

    def k(self) -> K:
        return K.from_bytes(self.take(16))

    def ks(self, n: int) -> list:
        return [self.k() for _ in range(n)]

    def done(self) -> None:
        if self.p != len(self.d):
            raise FormatError("trailing bytes")


def _u32(x): return struct.pack("<I", x)
def _u64(x): return struct.pack("<Q", x)
def _kb(xs): return b"".join(x.to_bytes() for x in xs)


# ----------------------------------------------------------------------------- verifying key

def encode_vk(vk: VerifyingKey) -> bytes:
    a = vk.abi
    prof = a.hash_profile.encode("ascii")
    out = [MAGIC_VK, bytes([VK_VERSION, len(prof)]), prof, bytes([a.ram_log_words, a.input_log_words,
           a.output_log_words]), _u64(a.max_code_words), vk.program_digest, _u64(vk.entry_pc), _u64(len(vk.code))]
    for pc in sorted(vk.code):
        out.append(_u64(pc) + _u32(vk.code[pc]))
    nz = sorted((w, v) for w, v in vk.m0_program.items() if v)
    out.append(_u64(len(nz)))
    for w, v in nz:
        out.append(_u64(w) + _u64(v))
    out.append(bytes([0 if vk.pcs == "ligerito" else 1, 0 if vk.pcs_profile == "provable-120" else 1, vk.pcs_r])
               + _u32(vk.pcs_t))
    return b"".join(out)


def decode_vk(data: bytes) -> VerifyingKey:
    r = Reader(data)
    if r.take(4) != MAGIC_VK or r.u8() != VK_VERSION:
        raise FormatError("bad vk magic or version")
    prof = r.take(r.u8()).decode("ascii")
    A, I, O = r.u8(), r.u8(), r.u8()
    maxc = r.u64()
    digest = r.take(32)
    entry = r.u64()
    ncode = r.u64()
    if ncode > maxc:
        raise FormatError("too many code words")
    code, prev = {}, -1
    for _ in range(ncode):
        pc, w = r.u64(), r.u32()
        if pc <= prev:
            raise FormatError("code not sorted")
        code[pc], prev = w, pc
    nm0 = r.u64()
    m0, prev = {}, -1
    for _ in range(nm0):
        w, v = r.u64(), r.u64()
        if w <= prev or not v:
            raise FormatError("data image not canonical")
        m0[w], prev = v, w
    mode, profile, pr, pt = r.u8(), r.u8(), r.u8(), r.u32()
    r.done()
    if mode > 1 or profile > 1:
        raise FormatError("bad pcs fields")
    vk = VerifyingKey(abi.Params(A, I, O, maxc, prof), code, entry, m0, ["ligerito", "transparent"][mode],
                      ["provable-120", "test"][profile], pr, pt, digest)
    return vk


# ----------------------------------------------------------------------------- instance

def encode_instance(inst) -> bytes:
    return (MAGIC_INSTANCE + bytes([1]) + _u64(inst.T) + _u64(len(inst.input)) + inst.input
            + _u64(len(inst.output)) + inst.output + _u64(inst.exit_code))


def decode_instance(data: bytes):
    from .protocol import PublicInstance
    r = Reader(data)
    if r.take(4) != MAGIC_INSTANCE or r.u8() != 1:
        raise FormatError("bad instance magic or version")
    T = r.u64()
    inp = r.take(r.u64())
    out = r.take(r.u64())
    ec = r.u64()
    r.done()
    return PublicInstance(T, inp, out, ec)


# ----------------------------------------------------------------------------- shapes

def _sc_w(sc: SumcheckProof) -> bytes:
    return b"".join(_kb(m) for m in sc.round_msgs)


def _sc_r(r: Reader, rounds: int, deg: int) -> SumcheckProof:
    return SumcheckProof([r.ks(deg) for _ in range(rounds)])


def twist_shape(p: tw.TwistParams, final: bool) -> dict:
    ngroups = p.p + 1 + (1 if final else 0)
    return dict(rw=(p.n + p.a, 3), rw_ev=p.p + 3, val=(p.n, 3), fin=(p.n, 2) if final else None,
                virt=(p.n, p.d + 1) if p.d > 1 else None, virt_ev=ngroups * p.d,
                oh=(p.n, 4), oh_ev=2 * (p.p + 1) * p.d)


def _twist_w(pr: tw.TwistProof) -> bytes:
    out = [_sc_w(pr.rw), _kb(pr.rw_evals), _sc_w(pr.val), _kb(pr.val_evals)]
    if pr.fin is not None:
        out += [_sc_w(pr.fin), _kb(pr.fin_evals)]
    if pr.virt is not None:
        out += [_sc_w(pr.virt.sc), _kb(pr.virt.evals)]
    out += [_sc_w(pr.onehot.sc), _kb([v for e in pr.onehot.evals for v in e])]
    return b"".join(out)


def _twist_r(r: Reader, p: tw.TwistParams, final: bool) -> tw.TwistProof:
    sh = twist_shape(p, final)
    rw = _sc_r(r, *sh["rw"])
    rw_ev = r.ks(sh["rw_ev"])
    val = _sc_r(r, *sh["val"])
    val_ev = r.ks(2)
    fin = fin_ev = None
    if final:
        fin = _sc_r(r, *sh["fin"])
        fin_ev = r.ks(2)
    virt = None
    if sh["virt"]:
        vs = _sc_r(r, *sh["virt"])
        virt = VirtProof(vs, r.ks(sh["virt_ev"]))
    ohs = _sc_r(r, *sh["oh"])
    flat = r.ks(sh["oh_ev"])
    oh = OneHotProof(ohs, [flat[i:i + 2] for i in range(0, len(flat), 2)])
    return tw.TwistProof(rw, rw_ev, val, val_ev, fin, fin_ev, None, virt, oh)


def _shout_shape(a, d, n, G):
    return dict(read=(a, 2), ra=G, virt=(n, d + 1) if d > 1 else None, virt_ev=d, oh=(n, 4), oh_ev=2 * d)


SHOUT_GROUPS = 6


def _shout_w(pr: ShoutProof) -> bytes:
    out = [_sc_w(pr.read), _kb(pr.ra_evals)]
    if pr.virt is not None:
        out += [_sc_w(pr.virt.sc), _kb(pr.virt.evals)]
    out += [_sc_w(pr.onehot.sc), _kb([v for e in pr.onehot.evals for v in e])]
    return b"".join(out)


def _shout_r(r: Reader, a, d, n) -> ShoutProof:
    sh = _shout_shape(a, d, n, SHOUT_GROUPS)
    read = _sc_r(r, *sh["read"])
    ra = r.ks(sh["ra"])
    virt = None
    if sh["virt"]:
        vs = _sc_r(r, *sh["virt"])
        virt = VirtProof(vs, r.ks(sh["virt_ev"]))
    ohs = _sc_r(r, *sh["oh"])
    flat = r.ks(sh["oh_ev"])
    return ShoutProof(read, ra, virt, OneHotProof(ohs, [flat[i:i + 2] for i in range(0, len(flat), 2)]))


# ----------------------------------------------------------------------------- Ligerito / ring switching

def _lig_w(pf: lg.LigeritoProof) -> bytes:
    out = list(pf.roots)
    for sc in pf.sumchecks:
        out.append(_sc_w(sc))
    for op in pf.openings:
        out.append(_u32(len(op.columns)))
        for col in op.columns:
            out.append(_kb(col))
        out.append(_u32(len(op.auth)))
        out += list(op.auth)
    out.append(_kb(pf.final))
    return b"".join(out)


def _lig_r(r: Reader, p: lg.LigeritoParams, dsz: int) -> lg.LigeritoProof:
    roots = [r.take(dsz) for _ in range(p.levels - 1)]
    scs = [_sc_r(r, p.ks[i], 2) for i in range(p.levels)]
    ops = []
    for i in range(p.levels):
        nc = r.u32()
        if nc > p.ts[i]:
            raise FormatError("too many opened columns")
        cols = [r.ks(1 << p.ks[i]) for _ in range(nc)]
        na = r.u32()
        if na > nc * 64 + 64:
            raise FormatError("too many authentication hashes")
        ops.append(lg.LevelOpening(cols, [r.take(dsz) for _ in range(na)]))
    return lg.LigeritoProof(roots, scs, ops, r.ks(1 << p.n_final))


# ----------------------------------------------------------------------------- proof

def encode_proof(vk: VerifyingKey, pr) -> bytes:
    sp = pr.spartan
    out = [MAGIC_PROOF, bytes([PROOF_VERSION, pr.log_t]), pr.root]
    for t in range(2):
        out.append(b"".join(_kb(m) for m in sp.outer_msgs[t]))
    for t in range(2):
        out.append(_kb(sp.outer_finals[t]))
    out += [_sc_w(sp.inner), sp.v_W.to_bytes(), _kb(sp.seg_vals), _sc_w(sp.xs_proof), _kb(sp.xs_vals)]
    out += [_kb(pr.reg_bits), _twist_w(pr.reg), _kb(pr.ram_bits), pr.ram_inc_wv.to_bytes(), _twist_w(pr.ram)]
    out += [_sc_w(pr.shift.sc), _kb(pr.shift.evals), _sc_w(pr.store.sc), _kb(pr.store.evals)]
    out += [_shout_w(pr.shout), _sc_w(pr.mosaic.sumcheck), pr.mosaic.v_G.to_bytes()]
    if vk.pcs == "transparent":
        G = pr.pcs_proof
        out.append(int("".join("1" if x else "0" for x in reversed(G)), 2).to_bytes((len(G) + 7) // 8, "little"))
    else:
        rs, lp = pr.pcs_proof
        out += [_kb(rs.s), _sc_w(rs.sumcheck), _lig_w(lp)]
    return b"".join(out)


def decode_proof(vk: VerifyingKey, data: bytes, T: int):
    from .protocol import Proof
    D = vk.derived
    I = D.instance(T)
    n, s = I.n, I.s
    r = Reader(data)
    if r.take(4) != MAGIC_PROOF or r.u8() != PROOF_VERSION:
        raise FormatError("bad proof magic or version")
    if r.u8() != n:
        raise FormatError("proof log T does not match the instance")
    dsz = vk.hasher.digest_size
    root = r.take(dsz)
    rho, nu = D.rho, D.nu
    outer = [[r.ks(3) for _ in range(rho + s)] for _ in range(2)]
    finals = [r.ks(3) for _ in range(2)]
    inner = _sc_r(r, nu, 2)
    v_W = r.k()
    seg_vals = r.ks(len(D.segments))
    xs_proof = _sc_r(r, 8 + s, 2)
    xs_vals = r.ks(2)
    spp = spartan.SpartanProof(outer, finals, inner, v_W, seg_vals, xs_proof, xs_vals)
    reg_bits = r.ks(3 * REG_A)
    reg = _twist_r(r, I.reg, False)
    ram_bits = r.ks(D.ram_a)
    y0 = r.k()
    ram = _twist_r(r, I.ram, True)
    shift = rt.RouterProof(_sc_r(r, n + 15, 4), r.ks(3))
    store = rt.RouterProof(_sc_r(r, n + 9, 6), r.ks(5))
    shout = _shout_r(r, D.rom_a, D.rom_d, n)
    mos = BatchProof(_sc_r(r, I.ell, 2), None)
    mos.v_G = r.k()
    if vk.pcs == "transparent":
        nb = (1 << I.ell) // 8 if I.ell >= 3 else 1
        v = int.from_bytes(r.take(nb), "little")
        pcs_proof = [(v >> i) & 1 for i in range(1 << I.ell)]
    else:
        p = D.ligerito_params(I.ell)
        s_ = r.ks(128)
        rsp = rsw.RingSwitchProof(s_, _sc_r(r, I.ell - 7, 2))
        pcs_proof = (rsp, _lig_r(r, p, dsz))
    r.done()
    return Proof(n, root, spp, reg_bits, reg, ram_bits, y0, ram, shift, store, shout, mos, pcs_proof)


# ----------------------------------------------------------------------------- size model

def pcs_free_k_count(n: int, ram_a: int, ram_d: int, rom_a: int, rom_d: int, ell: int, num_segments: int,
                     rho: int = 10, nu: int = 14, reg_d: int = 2) -> int:
    """Number of K elements of the proof outside the PCS opening (exact), as a function of the shape."""
    s = n - 2
    cnt = 2 * 3 * (rho + s) + 6 + 2 * nu + 1 + num_segments + 2 * (8 + s) + 2     # Spartan (06 6.7)
    cnt += 3 * REG_A
    for (a, d, p, fin) in ((REG_A, reg_d, 2, False), (ram_a, ram_d, 1, True)):
        ngroups = p + 1 + (1 if fin else 0)
        cnt += 3 * (n + a) + (p + 3) + 3 * n + 2
        if fin:
            cnt += 2 * n + 2
        if d > 1:
            cnt += (d + 1) * n + ngroups * d
        cnt += 4 * n + 2 * (p + 1) * d
    cnt += ram_a + 1
    cnt += 4 * (n + 15) + 3 + 6 * (n + 9) + 5
    cnt += 2 * rom_a + SHOUT_GROUPS + 4 * n + 2 * rom_d
    if rom_d > 1:
        cnt += (rom_d + 1) * n + rom_d
    cnt += 2 * ell + 1
    cnt += 128 + 2 * (ell - 7)          # ring switching
    return cnt


def ligerito_expected_bytes(p: lg.LigeritoParams, digest_size: int = 32) -> float:
    """Expected size of a LigeritoProof encoding (uniform random queries, sorted distinct)."""
    total = digest_size * (p.levels - 1) + 16 * (1 << p.n_final)
    for i in range(p.levels):
        N, t, k = 1 << p.log_codeword(i), p.ts[i], p.ks[i]
        distinct = N * (1 - (1 - 1 / N) ** t)
        depth = p.log_codeword(i)
        # expected auth hashes of a deduplicated multi-path: sum over levels of siblings not in the set
        auth = 0.0
        for lvl in range(depth):
            nodes = (1 << (depth - lvl))
            occ = nodes * (1 - (1 - 1 / nodes) ** t)
            # sibling absent probability ~ (1 - 1/nodes)^t
            auth += occ * (1 - 1 / nodes) ** t
        total += 8 + 16 * k * 2 + distinct * (16 << k) + auth * digest_size
    return total
