"""Spartan family reference model (docs/spec/06-spartan.md).

One code path covers Construction 1 / SIMD / BinarySpartan (T = 1 relation, no layout)
and Construction 2, Virtual Spartan (T = 2 relations, segment layout, optional cross-step).
"""

from __future__ import annotations

from dataclasses import dataclass

from .field import K
from .mle import bind_low, eq_eval, eq_table, mle_eval
from .mosaic import Claim
from .r1cs import R1CS, build_z, check_witness_bits, public_part, simd_satisfied
from .sumcheck import SumcheckProof, VerificationError, sumcheck_prove, sumcheck_verify
from .transcript import Transcript


# ---------------------------------------------------------------- data types

@dataclass(frozen=True)
class Segment:
    """Column segment: columns [block * 2^log_cols, (block+1) * 2^log_cols). kind: direct|virtual|pad."""
    seg_id: int
    kind: str
    log_cols: int
    block: int


@dataclass
class CrossStep:
    in_id: int
    out_id: int
    init: list   # public initial state, 2^lam bits
    fin: list    # public final state, 2^lam bits


@dataclass
class SpartanProof:
    outer_msgs: list          # [t][round] -> [g(t0), g(t2), g(t3)]
    outer_finals: list        # [t] -> [vA, vB, vC]
    inner: SumcheckProof
    v_W: K
    seg_vals: list            # one per non-pad segment, layout order
    xs_proof: SumcheckProof | None = None
    xs_vals: list | None = None   # [v_in, v_out]


def _u64(n: int) -> bytes:
    return n.to_bytes(8, "little")


def _interp(ys: list[K], r: K) -> K:
    """Lagrange interpolation through points t_0..t_{n-1}."""
    n, acc = len(ys), K.ZERO
    for k in range(n):
        num, den = K.ONE, K.ONE
        for j in range(n):
            if j != k:
                num = num * (r + K.t(j))
                den = den * (K.t(k) + K.t(j))
        acc = acc + ys[k] * num / den
    return acc


def _bits_of(v: int, n: int) -> list[K]:
    return [K((v >> k) & 1) for k in range(n)]


def check_layout(segs: list[Segment], nu: int) -> None:
    """Segments must be aligned, in range, pairwise disjoint, with distinct ids."""
    cols = 1 << (nu - 1)
    seen_ids, used = set(), []
    for s in segs:
        if s.kind not in ("direct", "virtual", "pad"):
            raise ValueError("bad segment kind")
        if s.seg_id in seen_ids:
            raise ValueError("duplicate segment id")
        seen_ids.add(s.seg_id)
        lo, hi = s.block << s.log_cols, (s.block + 1) << s.log_cols
        if s.log_cols < 0 or s.log_cols > nu - 1 or hi > cols:
            raise ValueError("segment out of range")
        for a, b in used:
            if lo < b and a < hi:
                raise ValueError("segments overlap")
        used.append((lo, hi))


def next_mle(a: list[K], b: list[K]) -> K:
    """MLE of N(a,b) = [int(b) = int(a)+1 and int(a) < 2^s - 1], LSB-first (C2).
    N~ = sum_i [prod_{j<i} a_j (1+b_j)] (1+a_i) b_i [prod_{j>i} eq(a_j,b_j)]  (0-indexed i)."""
    s = len(a)
    suffix = [K.ONE] * (s + 1)
    for j in range(s - 1, -1, -1):
        suffix[j] = suffix[j + 1] * (K.ONE + a[j] + b[j])
    acc, prefix = K.ZERO, K.ONE
    for i in range(s):
        acc = acc + prefix * (K.ONE + a[i]) * b[i] * suffix[i + 1]
        prefix = prefix * a[i] * (K.ONE + b[i])
    return acc


def xs_weights(tau_u: list[K], gamma: K, r_u: list[K]) -> tuple[K, K]:
    """MLEs at r_u of the public u-tables a_out, a_in of the cross-step sum-check."""
    prod_tau, prod_r, prod_nr = K.ONE, K.ONE, K.ONE
    for t, r in zip(tau_u, r_u):
        prod_tau, prod_r, prod_nr = prod_tau * t, prod_r * r, prod_nr * (K.ONE + r)
    a_out = eq_eval(tau_u, r_u) + prod_tau * prod_r + gamma * gamma * prod_r
    a_in = next_mle(tau_u, r_u) + gamma * prod_nr
    return a_out, a_in


def _lbl(P: bytes, *parts: bytes) -> bytes:
    return b"/".join((P,) + parts)


def _g_evals(E, A, B, C) -> list[K]:
    """g(t) = sum_i E(t)(A(t)B(t) + C(t)) at t_0..t_3, where T(t) = T[2i] + t (T[2i] + T[2i+1])."""
    acc = [K.ZERO] * 4
    for i in range(len(E) // 2):
        for k in range(4):
            t = K.t(k)
            vals = [T[2 * i] + t * (T[2 * i] + T[2 * i + 1]) for T in (E, A, B, C)]
            acc[k] = acc[k] + vals[0] * (vals[1] * vals[2] + vals[3])
    return acc


# ---------------------------------------------------------------- common transcript prefix

def _setup(transcript, P, T, rho, nu, s, nx, X, names):
    transcript.absorb_bytes(_lbl(P, b"shape"), b"".join(_u64(v) for v in (T, rho, nu, s, nx)))
    transcript.absorb_ks(_lbl(P, b"pub"), [K(int(v.v if isinstance(v, K) else v)) for row in X for v in row])
    return [transcript.challenge_ks(_lbl(P, b"tau", nm), rho + s) for nm in names]


def _fold_public(X, nu, r_inst):
    half = 1 << (nu - 1)
    out = [K.ZERO] * half
    if not X or not X[0]:
        out[0] = K.ONE
        return out
    eqi = eq_table(r_inst)
    for u, x in enumerate(X):
        pp = public_part(list(x), nu)
        for k in range(half):
            out[k] = out[k] + eqi[u] * pp[k]
    return out


# ---------------------------------------------------------------- prover

def prove(rels: list[R1CS], W: list[list[int]], X: list[list], transcript: Transcript, P: bytes = b"vsp",
          names: list[bytes] | None = None, segments: list[Segment] | None = None,
          cross: CrossStep | None = None, unchecked: bool = False):
    """Returns (SpartanProof, claims). `unchecked` skips the satisfiability check (tests only)."""
    T = len(rels)
    names = names or ([b"bin", b"fld"][:T] if T <= 2 else [b"r%d" % i for i in range(T)])
    rho, nu = rels[0].rho, rels[0].nu
    if any((r.rho, r.nu) != (rho, nu) for r in rels):
        raise ValueError("relations must share (rho, nu)")
    q = len(W)
    s = q.bit_length() - 1
    if q != 1 << s:
        raise ValueError("number of instances must be a power of two")
    check_witness_bits(W, nu)
    if not unchecked and not simd_satisfied(rels, W, X):
        raise ValueError("witness does not satisfy the SIMD R1CS")
    nx = len(X[0])
    if any(len(x) != nx for x in X):
        raise ValueError("public inputs must have equal length")
    if segments is not None:
        check_layout(segments, nu)

    tau = _setup(transcript, P, T, rho, nu, s, nx, X, names)

    # outer tables, index = row + 2^rho * instance
    zs = [build_z(w, x, nu) for w, x in zip(W, X)]
    tabs = []
    for t, R in enumerate(rels):
        cols = [[], [], []]
        for z in zs:
            for m, M in enumerate(R.mats):
                cols[m].extend(M.mul_vec(z))
        tabs.append([eq_table(tau[t])] + cols)
    cur = [K.ZERO] * T
    for t in range(T):
        E, A, B, C = tabs[t]
        ev = _g_evals(E, A, B, C)
        cur[t] = ev[0] + ev[1]
        if not unchecked and cur[t]:
            raise ValueError("outer claim is non-zero")
    msgs = [[] for _ in range(T)]
    r_row = [[] for _ in range(T)]
    r_inst = []
    for _ in range(rho):
        for t in range(T):
            ev = _g_evals(*tabs[t])
            msg = [ev[0], ev[2], ev[3]]
            transcript.absorb_ks(_lbl(P, b"outer", names[t], b"msg"), msg)
            r = transcript.challenge_k(_lbl(P, b"outer", names[t], b"row"))
            msgs[t].append(msg)
            r_row[t].append(r)
            tabs[t] = [bind_low(x, r) for x in tabs[t]]
    for _ in range(s):
        evs = [_g_evals(*tabs[t]) for t in range(T)]
        for t in range(T):
            msg = [evs[t][0], evs[t][2], evs[t][3]]
            transcript.absorb_ks(_lbl(P, b"outer", names[t], b"msg"), msg)
            msgs[t].append(msg)
        r = transcript.challenge_k(_lbl(P, b"outer", b"inst"))
        r_inst.append(r)
        tabs = [[bind_low(x, r) for x in tabs[t]] for t in range(T)]
    finals = [[tabs[t][1][0], tabs[t][2][0], tabs[t][3][0]] for t in range(T)]
    for t in range(T):
        transcript.absorb_ks(_lbl(P, b"outer", names[t], b"final"), finals[t])
    alpha = transcript.challenge_ks(_lbl(P, b"alpha"), 3 * T)

    # inner sum-check over columns
    v_star = K.ZERO
    Mcomb = [K.ZERO] * (1 << nu)
    for t, R in enumerate(rels):
        for m, M in enumerate(R.mats):
            a = alpha[3 * t + m]
            v_star = v_star + a * finals[t][m]
            ft = M.fold_rows(r_row[t])
            Mcomb = [x + a * y for x, y in zip(Mcomb, ft)]
    eqi = eq_table(r_inst)
    half = 1 << (nu - 1)
    wfold = [K.ZERO] * half
    for u, w in enumerate(W):
        for c in range(half):
            if w[c]:
                wfold[c] = wfold[c] + eqi[u]
    zfold = wfold + _fold_public(X, nu, r_inst)
    inner, r_y, _ = sumcheck_prove(v_star, [Mcomb, zfold], lambda v: v[0] * v[1], 2, transcript, _lbl(P, b"inner"))
    r_col = r_y[:nu - 1]
    v_W = mle_eval(wfold, r_col)
    transcript.absorb_k(_lbl(P, b"vw"), v_W)

    claims, seg_vals = [], []
    if segments is None:
        claims.append(Claim(-1, r_col + r_inst, v_W))
    else:
        for sg in segments:
            if sg.kind == "pad":
                continue
            tbl = _segment_table(W, sg)
            v = mle_eval(tbl, r_col[:sg.log_cols] + r_inst)
            transcript.absorb_k(_lbl(P, b"seg"), v)
            seg_vals.append(v)
            claims.append(Claim(sg.seg_id, r_col[:sg.log_cols] + r_inst, v))
    proof = SpartanProof(msgs, finals, inner, v_W, seg_vals)

    if cross is not None:
        _cross_prove(proof, claims, segments, cross, W, s, transcript, P, unchecked)
    return proof, claims


def _segment_table(W, sg: Segment) -> list[int]:
    off, n = sg.block << sg.log_cols, 1 << sg.log_cols
    return [row[off + y] for row in W for y in range(n)]


def _xs_setup(cross: CrossStep, segments, s, transcript, P):
    by_id = {sg.seg_id: sg for sg in segments or []}
    si, so = by_id.get(cross.in_id), by_id.get(cross.out_id)
    if si is None or so is None or si.kind == "pad" or so.kind == "pad" or si.log_cols != so.log_cols \
            or cross.in_id == cross.out_id:
        raise VerificationError("cross-step segments invalid")
    lam = si.log_cols
    if len(cross.init) != 1 << lam or len(cross.fin) != 1 << lam:
        raise VerificationError("cross-step public state has wrong length")
    transcript.absorb_ks(_lbl(P, b"xs", b"init"), [K(int(v.v if isinstance(v, K) else v)) for v in cross.init])
    transcript.absorb_ks(_lbl(P, b"xs", b"fin"), [K(int(v.v if isinstance(v, K) else v)) for v in cross.fin])
    tau = transcript.challenge_ks(_lbl(P, b"xs", b"tau"), lam + s)
    gamma = transcript.challenge_k(_lbl(P, b"xs", b"gamma"))
    claim = gamma * mle_eval(list(cross.init), tau[:lam]) + gamma * gamma * mle_eval(list(cross.fin), tau[:lam])
    return si, so, lam, tau, gamma, claim


def _cross_prove(proof, claims, segments, cross, W, s, transcript, P, unchecked):
    si, so, lam, tau, gamma, claim = _xs_setup(cross, segments, s, transcript, P)
    q, n = 1 << s, 1 << lam
    eqk, equ = eq_table(tau[:lam]), eq_table(tau[lam:])
    a_out_u = [(equ[u] if u != q - 1 else K.ZERO) + (gamma * gamma if u == q - 1 else K.ZERO) for u in range(q)]
    a_in_u = [(equ[u - 1] if u >= 1 else K.ZERO) + (gamma if u == 0 else K.ZERO) for u in range(q)]
    tbl_in, tbl_out = _segment_table(W, si), _segment_table(W, so)
    size = n * q
    E = [eqk[i % n] for i in range(size)]
    Ao = [a_out_u[i // n] for i in range(size)]
    Ai = [a_in_u[i // n] for i in range(size)]
    if unchecked:  # a cheating prover proves the *true* sum instead of the public claim
        claim = K.ZERO
        for i in range(size):
            claim = claim + E[i] * (Ao[i] * tbl_out[i] + Ai[i] * tbl_in[i])
    f = lambda v: v[0] * (v[1] * v[2] + v[3] * v[4])
    sc, r, fin = sumcheck_prove(claim, [E, Ao, [K(b) for b in tbl_out], Ai, [K(b) for b in tbl_in]], f, 2,
                                transcript, _lbl(P, b"xs", b"sc"))
    v_out, v_in = fin[2], fin[4]
    transcript.absorb_ks(_lbl(P, b"xs", b"final"), [v_in, v_out])
    proof.xs_proof, proof.xs_vals = sc, [v_in, v_out]
    claims.append(Claim(cross.in_id, r, v_in))
    claims.append(Claim(cross.out_id, r, v_out))


# ---------------------------------------------------------------- verifier

def verify(rels: list[R1CS], s: int, X: list[list], proof: SpartanProof, transcript: Transcript,
           P: bytes = b"vsp", names: list[bytes] | None = None, segments: list[Segment] | None = None,
           cross: CrossStep | None = None):
    """Returns the output claims. Raises VerificationError."""
    T = len(rels)
    names = names or ([b"bin", b"fld"][:T] if T <= 2 else [b"r%d" % i for i in range(T)])
    rho, nu = rels[0].rho, rels[0].nu
    if not X:
        nx = 0
    else:
        q = 1 << s
        if len(X) != q:
            raise VerificationError("wrong number of public inputs")
        nx = len(X[0])
        if any(len(x) != nx for x in X):
            raise VerificationError("public inputs must have equal length")
    if segments is not None:
        check_layout(segments, nu)
    if len(proof.outer_msgs) != T or len(proof.outer_finals) != T:
        raise VerificationError("malformed proof")
    if any(len(m) != rho + s for m in proof.outer_msgs):
        raise VerificationError("wrong number of outer rounds")
    tau = _setup(transcript, P, T, rho, nu, s, nx, X, names)

    def step(t, msg, r):
        if len(msg) != 3 or not all(isinstance(v, K) for v in msg):
            raise VerificationError("malformed outer message")
        ys = [msg[0], cur[t] + msg[0], msg[1], msg[2]]
        cur[t] = _interp(ys, r)

    cur = [K.ZERO] * T
    r_row = [[] for _ in range(T)]
    r_inst = []
    for i in range(rho):
        for t in range(T):
            msg = proof.outer_msgs[t][i]
            transcript.absorb_ks(_lbl(P, b"outer", names[t], b"msg"), msg)
            r = transcript.challenge_k(_lbl(P, b"outer", names[t], b"row"))
            step(t, msg, r)
            r_row[t].append(r)
    for i in range(s):
        for t in range(T):
            transcript.absorb_ks(_lbl(P, b"outer", names[t], b"msg"), proof.outer_msgs[t][rho + i])
        r = transcript.challenge_k(_lbl(P, b"outer", b"inst"))
        for t in range(T):
            step(t, proof.outer_msgs[t][rho + i], r)
        r_inst.append(r)
    for t in range(T):
        fv = proof.outer_finals[t]
        if len(fv) != 3 or not all(isinstance(v, K) for v in fv):
            raise VerificationError("malformed terminal values")
        if cur[t] != eq_eval(tau[t], r_row[t] + r_inst) * (fv[0] * fv[1] + fv[2]):
            raise VerificationError("outer sum-check final check failed")
        transcript.absorb_ks(_lbl(P, b"outer", names[t], b"final"), fv)
    alpha = transcript.challenge_ks(_lbl(P, b"alpha"), 3 * T)
    v_star = K.ZERO
    for t in range(T):
        for m in range(3):
            v_star = v_star + alpha[3 * t + m] * proof.outer_finals[t][m]
    r_y, e = sumcheck_verify(v_star, nu, 2, proof.inner, transcript, _lbl(P, b"inner"))
    mf = K.ZERO
    for t, R in enumerate(rels):
        for m, M in enumerate(R.mats):
            mf = mf + alpha[3 * t + m] * M.mle(r_row[t], r_y)
    r_col = r_y[:nu - 1]
    top = r_y[nu - 1]
    if nx == 0:
        pub = K.ONE
        for rc in r_col:
            pub = pub * (K.ONE + rc)
    else:
        pub = mle_eval(_fold_public(X, nu, r_inst), r_col)
    v_z = (K.ONE + top) * proof.v_W + top * pub
    if e != mf * v_z:
        raise VerificationError("inner sum-check final check failed")
    transcript.absorb_k(_lbl(P, b"vw"), proof.v_W)

    claims = []
    if segments is None:
        claims.append(Claim(-1, r_col + r_inst, proof.v_W))
    else:
        real = [sg for sg in segments if sg.kind != "pad"]
        if len(proof.seg_vals) != len(real):
            raise VerificationError("wrong number of segment claims")
        acc = K.ZERO
        for sg, v in zip(real, proof.seg_vals):
            transcript.absorb_k(_lbl(P, b"seg"), v)
            qi = r_col[sg.log_cols:]
            acc = acc + eq_eval(qi, _bits_of(sg.block, nu - 1 - sg.log_cols)) * v
            claims.append(Claim(sg.seg_id, r_col[:sg.log_cols] + r_inst, v))
        if acc != proof.v_W:
            raise VerificationError("segment claims inconsistent with v_W")
    if cross is not None:
        si, so, lam, txs, gamma, claim = _xs_setup(cross, segments, s, transcript, P)
        if proof.xs_proof is None or proof.xs_vals is None or len(proof.xs_vals) != 2:
            raise VerificationError("missing cross-step proof")
        r, e = sumcheck_verify(claim, lam + s, 2, proof.xs_proof, transcript, _lbl(P, b"xs", b"sc"))
        v_in, v_out = proof.xs_vals
        a_out, a_in = xs_weights(txs[lam:], gamma, r[lam:])
        if e != eq_eval(txs[:lam], r[:lam]) * (a_out * v_out + a_in * v_in):
            raise VerificationError("cross-step final check failed")
        transcript.absorb_ks(_lbl(P, b"xs", b"final"), [v_in, v_out])
        claims.append(Claim(cross.in_id, r, v_in))
        claims.append(Claim(cross.out_id, r, v_out))
    return claims
