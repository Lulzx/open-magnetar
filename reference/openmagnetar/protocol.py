"""Full open-magnetar prover and verifier (docs/spec/11-protocol.md).

Composition (Construction 3): commit G -> Virtual Spartan -> register Twist -> RAM Twist (final
memory) -> shift router -> store router -> bytecode Shout -> Mosaic batching -> ring switching ->
Ligerito (or the test-only transparent mock).
"""

from __future__ import annotations

from dataclasses import dataclass

from . import abi, bytecode as bc, cpu_circuit as cpu, router as rt, spartan, twist as tw
from .field import K
from .keygen import REG_A, WORD_BITS, Derived, Instance, VerifyingKey
from .mle import eq_eval, eq_table, mle_eval
from .mosaic import BatchProof, Claim, batch_prove, batch_verify, build_G
from .onehot import EvalClaim, bits_of, comp_tables
from .pcs import BitPCS, Commitment
from .shout import ShoutClaims, ShoutParams, shout_prove, shout_verify
from .sumcheck import VerificationError
from .transcript import Transcript, u64le

LABEL = b"openmagnetar/zkvm/v1"
REG_IDX_COLS = ("rs1", "rs2", "rd")


@dataclass
class PublicInstance:
    T: int
    input: bytes
    output: bytes
    exit_code: int


@dataclass
class Proof:
    log_t: int
    root: bytes
    spartan: spartan.SpartanProof
    reg_bits: list
    reg: tw.TwistProof
    ram_bits: list
    ram_inc_wv: K
    ram: tw.TwistProof
    shift: rt.RouterProof
    store: rt.RouterProof
    shout: object
    mosaic: BatchProof
    pcs_proof: object       # transparent: list[int] (G); ligerito: (RingSwitchProof, LigeritoProof)


# ------------------------------------------------------------------------------ shared helpers

def _statement(tr: Transcript, vk: VerifyingKey, inst: PublicInstance) -> None:
    tr.absorb_bytes(b"vk/digest", vk.digest())
    tr.absorb_bytes(b"stmt/T", u64le(inst.T))
    tr.absorb_bytes(b"stmt/input", inst.input)
    tr.absorb_bytes(b"stmt/output", inst.output)
    tr.absorb_bytes(b"stmt/exit", u64le(inst.exit_code))


def _absorb_commitment(vk: VerifyingKey, I: Instance, root: bytes, tr: Transcript):
    if vk.pcs == "transparent":
        tr.absorb_bytes(b"pcs/params", b"transparent")
        tr.absorb_bytes(b"pcs/root", root)
        return None
    pcs = BitPCS(vk.derived.ligerito_params(I.ell), vk.hasher)
    pcs.pcs.absorb_commitment(Commitment(root, pcs.pcs.p.n), tr)
    return pcs


def _transparent_root(vk: VerifyingKey, G: list) -> bytes:
    b = int("".join("1" if x else "0" for x in reversed(G)), 2).to_bytes((len(G) + 7) // 8, "little")
    return vk.hasher.digest(b"openmagnetar/transparent-G/v1" + b)


def _m0_words(vk: VerifyingKey, data: bytes) -> dict:
    return abi.build_m0(vk.m0_program, data, vk.abi)


def _m0_eval(words: dict, A: int):
    nz = [(k, v) for k, v in words.items() if v]

    def f(pt):
        rk, ro = pt[:A], pt[A:]
        eo = eq_table(ro)
        acc = K.ZERO
        for k, v in nz:
            s = 0
            for o in range(64):
                if (v >> o) & 1:
                    s ^= eo[o].v
            acc = acc + eq_eval(rk, bits_of(k, A)) * K(s)
        return acc
    return f


def _seg_claims(D: Derived, claims: list):
    """Split Spartan output claims: (virtual-by-name, direct in layout order, cross-step claims)."""
    nseg = len(D.segments)
    if len(claims) != nseg + 2:
        raise VerificationError("unexpected number of Spartan claims")
    virt, direct = {}, []
    for sg, cl in zip(D.segments, claims[:nseg]):
        if sg.kind == "virtual":
            virt[sg.name] = cl
        else:
            direct.append(cl)
    return virt, direct, claims[nseg:]


def _same_point(virt: dict, names, ol: int):
    pts = [list(virt[nm].point) for nm in names]
    if any(p != pts[0] for p in pts):
        raise VerificationError("virtual claims at different points")
    return pts[0][:ol], pts[0][ol:]


def _to_mosaic(I: Instance, ec: EvalClaim) -> Claim:
    return Claim(I.ids[ec.poly], ec.point, ec.value)


def _ram_bits_ok(r_o: list, bits: list, v_ridx: K, A: int) -> bool:
    eo = eq_table(r_o)
    acc = K.ZERO
    for t in range(A):
        acc = acc + eo[t] * bits[t]
    return acc == v_ridx


class _Plan:
    """Bytecode Shout table with point-dependent derived columns, and the claim groups (spec 11.7)."""

    def __init__(self, D: Derived, n: int, virt: dict, reg_bits: list, sh_claims: list, st_q: EvalClaim):
        N, rows = D.N, 1 << D.rom_a
        self.table = []
        for nm in REG_IDX_COLS:
            for t in range(6):
                self.table.append([K((D.rom[k][nm] >> t) & 1) for k in range(N)] + [K.ZERO] * (rows - N))
        self.groups = []

        def derived(field_, rho):
            eq = eq_table(rho)
            if len(eq) != cpu.FIELD[field_][1]:
                raise VerificationError("bad selector point length")
            col = []
            for k in range(N):
                v, acc, o = D.rom_fields[k][field_], 0, 0
                while v:
                    if v & 1:
                        acc ^= eq[o].v
                    v >>= 1
                    o += 1
                col.append(K(acc))
            self.table.append(col + [K.ZERO] * (rows - N))
            return len(self.table) - 1

        def group(c, specs, pre_cols=(), pre_rv=()):
            cols, rv = list(pre_cols), list(pre_rv)
            for field_, rho, val in specs:
                cols.append(derived(field_, rho))
                rv.append(val)
            if len(c) != n:
                raise VerificationError("bad cycle point length")
            self.groups.append(ShoutClaims(list(c), cols, rv, None))

        def spartan_group(fields, pre_cols=(), pre_rv=()):
            ol = cpu.FIELD[fields[0]][1].bit_length() - 1
            pts = [list(virt[f].point) for f in fields]
            if any(p[ol:] != pts[0][ol:] for p in pts):
                raise VerificationError("shout group at different cycle points")
            group(pts[0][ol:], [(f, virt[f].point[:ol], virt[f].value) for f in fields], pre_cols, pre_rv)

        spartan_group(["imm", "kc", "rpc", "rf", "Q_lo"], range(18), reg_bits)
        spartan_group(["upc", "seq", "tgt"])
        spartan_group(["Q_hi"])
        spartan_group(["st_w"])
        qlo, qhi = sh_claims[1], sh_claims[2]
        group(qlo.point[6:], [("Q_lo", qlo.point[:6], qlo.value), ("Q_hi", qhi.point[:3], qhi.value)])
        group(st_q.point[2:], [("st_w", st_q.point[:2], st_q.value)])
        self.params = ShoutParams("shout/bytecode", D.rom_a, D.rom_d, n)


def _mosaic_claims(I, direct, xs, reg_out, ram_out, r_o, r_c, y0, sh_claims, st_claims, shout_claims):
    out = list(direct) + list(xs)
    out += [_to_mosaic(I, c) for c in reg_out.claims]
    out += [_to_mosaic(I, c) for c in ram_out.claims]
    out.append(_to_mosaic(I, EvalClaim("twist/ram/inc", list(r_o) + list(r_c), y0)))
    out.append(_to_mosaic(I, EvalClaim("shsrc", sh_claims[0].point, sh_claims[0].value)))
    out.append(_to_mosaic(I, EvalClaim("stc", st_claims[0].point, st_claims[0].value)))
    for b, c in enumerate(st_claims[2:]):
        out.append(_to_mosaic(I, EvalClaim("off", [K(b & 1), K((b >> 1) & 1)] + list(c.point), c.value)))
    out += [_to_mosaic(I, c) for c in shout_claims]
    return out


# ------------------------------------------------------------------------------ prover

@dataclass
class Execution:
    instance: PublicInstance
    trace: list
    exit_code: int
    m0: dict


def execute(vk: VerifyingKey, public_input: bytes, max_cycles: int = 1 << 20) -> Execution:
    D = vk.derived
    m0 = _m0_words(vk, public_input)
    vm = bc.VirtualMachine(D.program, m0, vk.abi.ram_log_words).run_padded(max_cycles)
    output = abi.extract_output(vm.ram, vk.abi)
    return Execution(PublicInstance(len(vm.trace), public_input, output, vm.exit_code), vm.trace, vm.exit_code, m0)


def prove(pk: VerifyingKey, public_input: bytes, private_input: bytes | None = None, **kw) -> Proof:
    return prove_instance(pk, public_input, private_input, **kw)[1]


def prove_instance(vk: VerifyingKey, public_input: bytes, private_input: bytes | None = None, *,
                   hooks: dict | None = None):
    """Returns (public instance, proof).  `hooks` (tests only): {"trace": fn(trace) that mutates the
    execution trace (a cheating prover)}; the Spartan satisfiability check is then skipped."""
    if private_input is not None:
        raise ValueError("v1 has no private input: the input is public (spec 14.1)")
    hooks = hooks or {}
    D = vk.derived
    ex = execute(vk, public_input)
    inst = ex.instance
    I = D.instance(inst.T)
    n, s = I.n, I.s
    trace = ex.trace
    if hooks.get("trace"):
        hooks["trace"](trace)
    public = cpu.public_inputs(D.program, ex.exit_code)
    W = cpu.witness(trace, D.cpu_params, ex.exit_code)

    reg_wit, reg_info = tw.build_witness(
        I.reg, [0] * 64, [[r["rs1"] for r in trace], [r["rs2"] for r in trace]],
        [r["rd"] for r in trace], [r["rd_val"] for r in trace])
    ram_a = D.ram_a
    m0_list = [ex.m0.get(k, 0) for k in range(1 << ram_a)]
    ridx = [r["ram_idx"] for r in trace]
    ram_wit, _ = tw.build_witness(I.ram, m0_list, [ridx], ridx, [r["ram_new"] for r in trace])
    sh_wit = rt.shift_witness(
        [(r["shift_src"], None if r["shift_amt"] is None or r["shift_kind"] is None
          else (r["shift_amt"], r["shift_kind"])) for r in trace], WORD_BITS)
    st_wit = rt.store_witness(
        [(r["ram_old"], r["store_src"], None if r["store_width"] is None else (r["store_width"], r["store_off"]))
         for r in trace], WORD_BITS)
    # the offset bits are the circuit's `off` segment, defined on every cycle (not only on stores)
    st_wit["abits"] = [[(r["store_off"] >> b) & 1 for r in trace] for b in range(3)]
    sh_comps = comp_tables([r["upc"] for r in trace], D.rom_a, D.rom_d)

    tables = {}
    for i, sg in enumerate(D.spartan_segments):
        if sg.kind == "direct":
            tables[i] = spartan._segment_table(W, sg)
    for x, comps in (("ra0", reg_wit.ra[0]), ("ra1", reg_wit.ra[1]), ("wa", reg_wit.wa)):
        for i, c in enumerate(comps):
            tables[I.ids[f"twist/reg/{x}/{i + 1}"]] = c
    tables[I.ids["twist/reg/inc"]] = reg_wit.inc
    for i, c in enumerate(ram_wit.ra[0]):
        tables[I.ids[f"twist/ram/ra0/{i + 1}"]] = c
    tables[I.ids["twist/ram/inc"]] = ram_wit.inc
    for i, c in enumerate(sh_comps):
        tables[I.ids[f"shout/bytecode/ra/{i + 1}"]] = c
    G = build_G(I.layout, tables)

    # step 1: statement, commitment
    tr = Transcript(LABEL, vk.hasher)
    _statement(tr, vk, inst)
    pcs = st = None
    if vk.pcs == "transparent":
        root = _transparent_root(vk, G)
        _absorb_commitment(vk, I, root, tr)
    else:
        pcs = BitPCS(D.ligerito_params(I.ell), vk.hasher)
        cm, st = pcs.commit(G, tr)
        root = cm.root

    # step 2: Virtual Spartan
    X = [[] for _ in range(1 << s)]
    cross = spartan.CrossStep(D.seg_id["S_in"], D.seg_id["S_out"], cpu.init_vector(public), cpu.fin_vector(public))
    sp_proof, sp_claims = spartan.prove(D.rels, W, X, tr, b"vsp", None, D.spartan_segments, cross,
                                        unchecked=bool(hooks.get("trace")))
    virt, direct, xs = _seg_claims(D, sp_claims)

    # step 3: register Twist
    r_o, r_c = _same_point(virt, ["v1", "v2", "rdv"], 6)
    honest = tw.honest_claims(I.reg, reg_info, r_o, r_c)
    reg_claims = tw.TwistClaims(r_o, r_c, [virt["v1"].value, virt["v2"].value], virt["rdv"].value, honest.bits)
    reg_bits = [v for row in honest.bits for v in row]
    reg_proof, reg_out = tw.twist_prove(I.reg, [0] * 64, reg_wit, reg_claims, tr, b"twist/reg")

    # step 4: RAM Twist with final memory; Inc claim at the Spartan point
    r_oR, r_cR = _same_point(virt, ["rw", "ridx"], 6)
    ram_bits = [mle_eval([(a >> t) & 1 for a in ridx], r_cR) for t in range(ram_a)]
    y0 = mle_eval(ram_wit.inc, r_oR + r_cR)
    tr.absorb_k(b"twist/ram/incwv", y0)
    ram_claims = tw.TwistClaims(r_oR, r_cR, [virt["rw"].value], virt["rw"].value + y0, [ram_bits, ram_bits])
    O = vk.abi.output_log_words
    final = tw.FinalMem(O, D.mm.output_base >> O, abi.encode_region(inst.output, O))
    ram_proof, ram_out = tw.twist_prove(I.ram, m0_list, ram_wit, ram_claims, tr, b"twist/ram", final=final)

    # step 5: routers
    r_oY, r_cY = _same_point(virt, ["Y"], 6)
    sh_proof, sh_claims = rt.shift_prove_fast(n, sh_wit, r_oY, r_cY, virt["Y"].value, tr, b"router/shift", WORD_BITS)
    st_proof, st_claims = rt.store_prove_fast(n, st_wit, r_oR, r_cR, y0, tr, b"router/store", WORD_BITS)

    # step 6: bytecode Shout
    plan = _Plan(D, n, virt, reg_bits, sh_claims, st_claims[1])
    shout_proof, shout_claims = shout_prove(plan.params, plan.table, sh_comps, plan.groups, tr, b"shout/bytecode")

    # step 7: Mosaic, ring switching, PCS
    mclaims = _mosaic_claims(I, direct, xs, reg_out, ram_out, r_oR, r_cR, y0, sh_claims, st_claims, shout_claims)
    batch, r_G, v_G = batch_prove(I.layout, mclaims, G, tr)
    if vk.pcs == "transparent":
        pcs_proof = list(G)
    else:
        y, pcs_proof = pcs.open(st, r_G, tr)
        if y != v_G:
            raise ValueError("internal error: G(r_G) != v_G")
    return inst, Proof(n, root, sp_proof, reg_bits, reg_proof, ram_bits, y0, ram_proof, sh_proof, st_proof,
                       shout_proof, batch, pcs_proof)


# ------------------------------------------------------------------------------ verifier

def verify(vk: VerifyingKey, instance: PublicInstance, proof) -> bool:
    """Accept or reject.  Any malformed or inconsistent input is a rejection (returns False)."""
    try:
        if isinstance(proof, (bytes, bytearray)):
            from . import proof_format as pf
            proof = pf.decode_proof(vk, bytes(proof), instance.T)
        verify_strict(vk, instance, proof)
        return True
    except Exception:       # noqa: BLE001  VerificationError, malformed encodings, bad shapes
        return False


def verify_strict(vk: VerifyingKey, inst: PublicInstance, proof: Proof) -> None:
    D = vk.derived
    if not (0 <= inst.exit_code < 1 << 64):
        raise VerificationError("bad exit code")
    I = D.instance(inst.T)
    if proof.log_t != I.n:
        raise VerificationError("proof is for a different T")
    n, s = I.n, I.s
    words = abi.encode_region(inst.output, vk.abi.output_log_words)
    m0 = _m0_words(vk, inst.input)
    public = cpu.public_inputs(D.program, inst.exit_code)

    tr = Transcript(LABEL, vk.hasher)
    _statement(tr, vk, inst)
    pcs = _absorb_commitment(vk, I, proof.root, tr)

    cross = spartan.CrossStep(D.seg_id["S_in"], D.seg_id["S_out"], cpu.init_vector(public), cpu.fin_vector(public))
    sp_claims = spartan.verify(D.rels, s, [], proof.spartan, tr, b"vsp", None, D.spartan_segments, cross)
    virt, direct, xs = _seg_claims(D, sp_claims)

    r_o, r_c = _same_point(virt, ["v1", "v2", "rdv"], 6)
    if len(proof.reg_bits) != 3 * REG_A:
        raise VerificationError("bad register bit claims")
    bits = [list(proof.reg_bits[6 * x:6 * x + 6]) for x in range(3)]
    reg_claims = tw.TwistClaims(r_o, r_c, [virt["v1"].value, virt["v2"].value], virt["rdv"].value, bits)
    reg_out = tw.twist_verify(I.reg, lambda pt: K.ZERO, reg_claims, proof.reg, tr, b"twist/reg")

    ram_a = D.ram_a
    r_oR, r_cR = _same_point(virt, ["rw", "ridx"], 6)
    if len(proof.ram_bits) != ram_a:
        raise VerificationError("bad RAM address-bit claims")
    if not _ram_bits_ok(r_oR, proof.ram_bits, virt["ridx"].value, ram_a):
        raise VerificationError("RAM address bits inconsistent with the ridx segment")
    y0 = proof.ram_inc_wv
    tr.absorb_k(b"twist/ram/incwv", y0)
    ram_claims = tw.TwistClaims(r_oR, r_cR, [virt["rw"].value], virt["rw"].value + y0,
                                [list(proof.ram_bits), list(proof.ram_bits)])
    O = vk.abi.output_log_words
    final = tw.FinalMem(O, D.mm.output_base >> O, words)
    ram_out = tw.twist_verify(I.ram, _m0_eval(m0, ram_a), ram_claims, proof.ram, tr, b"twist/ram", final=final)

    r_oY, r_cY = _same_point(virt, ["Y"], 6)
    sh_claims = rt.shift_verify(n, r_oY, r_cY, virt["Y"].value, proof.shift, tr, b"router/shift", WORD_BITS)
    st_claims = rt.store_verify(n, r_oR, r_cR, y0, proof.store, tr, b"router/store", WORD_BITS)

    plan = _Plan(D, n, virt, [v for row in bits for v in row], sh_claims, st_claims[1])
    shout_claims = shout_verify(plan.params, plan.table, plan.groups, proof.shout, tr, b"shout/bytecode")

    mclaims = _mosaic_claims(I, direct, xs, reg_out, ram_out, r_oR, r_cR, y0, sh_claims, st_claims, shout_claims)
    r_G, v_G = batch_verify(I.layout, mclaims, proof.mosaic, tr)
    if vk.pcs == "transparent":
        G = proof.pcs_proof
        if len(G) != 1 << I.ell or any(b not in (0, 1) for b in G) or _transparent_root(vk, G) != proof.root:
            raise VerificationError("transparent opening does not match the commitment")
        if mle_eval(G, r_G) != v_G:
            raise VerificationError("transparent opening: G(r_G) != v_G")
    else:
        pcs.verify(Commitment(proof.root, pcs.pcs.p.n), r_G, v_G, proof.pcs_proof, tr)
