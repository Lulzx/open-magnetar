"""BinaryTwist (docs/spec/07-twist-shout.md section 7.5).

Address component tables: see onehot.py.  Inc table: index o + 2^ell * j.
Memory M0 table: index k + 2^a * o (k low, C2).
"""

from __future__ import annotations

from dataclasses import dataclass

from .field import K
from .mle import eq_table, eq_eval, mle_eval
from .onehot import (EvalClaim, OneHotProof, VirtGroup, VirtProof, VirtTerm, bits_of,
                     comp_tables, full_table, onehot_prove, onehot_verify, virt_prove,
                     virt_verify)
from .sumcheck import SumcheckProof, sumcheck_prove, sumcheck_verify, VerificationError
from .transcript import Transcript


@dataclass
class TwistParams:
    name: str
    a: int
    d: int
    p: int
    n: int
    ell: int = 6        # words have 2^ell bits


@dataclass
class TwistClaims:
    r_o: list           # K^ell
    r_c: list           # K^n
    rv: list            # p claimed values rv_s~(r_o, r_c)
    wv: K               # wv~(r_o, r_c)
    bits: list          # bits[x][t]: address bit t of address x (x < p reads, x = p write) at r_c


@dataclass
class FinalMem:
    m: int              # output region has 2^m words
    s_out: int          # high (a - m) bits of the region's first word index
    words: list         # 2^m public output words (ints)


@dataclass
class TwistWitness:
    ra: list            # ra[s] = list of d component tables
    wa: list            # list of d component tables
    inc: list           # 0/1 table, index o + 2^ell * j


@dataclass
class TwistProof:
    rw: SumcheckProof
    rw_evals: list      # [ra_0..ra_{p-1}, wa, V, I]
    val: SumcheckProof
    val_evals: list     # [wa~(r_k, s), I~(r_o, s)]
    fin: SumcheckProof | None
    fin_evals: list | None
    inc_extra: K | None
    virt: VirtProof | None
    onehot: OneHotProof


@dataclass
class TwistOutput:
    claims: list
    inc_extra: EvalClaim | None


# ----------------------------------------------------------------- helpers

def lt_eval(x: list, y: list) -> K:
    """MLE of LT(x, y) = [x < y] (C2 order, x_1 = LSB): O(n) field operations.
    LT~(x,y) = sum_i (1 + x_i) y_i prod_{m > i} (1 + x_m + y_m)."""
    acc, suffix = K.ZERO, K.ONE
    for i in range(len(x) - 1, -1, -1):
        acc = acc + (K.ONE + x[i]) * y[i] * suffix
        suffix = suffix * (K.ONE + x[i] + y[i])
    return acc


def lt_table(y: list) -> list:
    n = len(y)
    return [lt_eval(bits_of(j, n), y) for j in range(1 << n)]


def comp_names_tw(params: TwistParams) -> list:
    nm = []
    for s in range(params.p):
        nm += [f"{params.name}/ra{s}/{i + 1}" for i in range(params.d)]
    nm += [f"{params.name}/wa/{i + 1}" for i in range(params.d)]
    return nm


def word_table(words: list, ell: int) -> list:
    return [(w >> o) & 1 for w in words for o in range(1 << ell)]


def build_witness(params: TwistParams, m0: list, reads: list, writes: list, new_words: list):
    """From an access trace (reads[s][j], writes[j], new_words[j]) build the witness
    and the honest values.  Returns (witness, info)."""
    a, d, p, n, ell = params.a, params.d, params.p, params.n, params.ell
    T, L = 1 << n, 1 << ell
    state = list(m0)
    rv = [[0] * T for _ in range(p)]
    wv, inc = [0] * T, [0] * T
    for j in range(T):
        for s in range(p):
            rv[s][j] = state[reads[s][j]]
        old = state[writes[j]]
        inc[j] = old ^ new_words[j]
        state[writes[j]] = new_words[j]
        wv[j] = new_words[j]
    wit = TwistWitness([comp_tables(reads[s], a, d) for s in range(p)],
                       comp_tables(writes, a, d), word_table(inc, ell))
    info = dict(rv=rv, wv=wv, inc=inc, final=state, reads=reads, writes=writes)
    return wit, info


def honest_claims(params: TwistParams, info: dict, r_o: list, r_c: list) -> TwistClaims:
    a, p, n, ell = params.a, params.p, params.n, params.ell
    pt = list(r_o) + list(r_c)
    rv = [mle_eval(word_table(info["rv"][s], ell), pt) for s in range(p)]
    wv = mle_eval(word_table(info["wv"], ell), pt)
    addrs = list(info["reads"]) + [info["writes"]]
    bits = [[mle_eval([(ad >> t) & 1 for ad in addrs[x]], r_c) for t in range(a)]
            for x in range(p + 1)]
    return TwistClaims(list(r_o), list(r_c), rv, wv, bits)


def m0_table(m0: list, a: int, ell: int) -> list:
    NK = 1 << a
    return [(m0[k] >> o) & 1 for o in range(1 << ell) for k in range(NK)]


def out_table(words: list, ell: int) -> list:
    return [(w >> o) & 1 for o in range(1 << ell) for w in words]


def _absorb(tr, label, c: TwistClaims):
    tr.absorb_ks(label + b"/point_o", c.r_o)
    tr.absorb_ks(label + b"/point_c", c.r_c)
    tr.absorb_ks(label + b"/rv", c.rv)
    tr.absorb_k(label + b"/wv", c.wv)
    tr.absorb_ks(label + b"/bits", [v for row in c.bits for v in row])


def _coeffs(tr, label, p, a):
    alpha0, alphas = [], []
    for x in range(p + 1):
        alpha0.append(tr.challenge_nonzero_k(label + b"/alpha0"))
        alphas.append(tr.challenge_ks(label + b"/alpha", a))
    beta = tr.challenge_ks(label + b"/beta", p + 1)
    return alpha0, alphas, beta


def _phi_k(alpha0, alphas, a):
    out = []
    for k in range(1 << a):
        v = alpha0
        for t in range(a):
            if (k >> t) & 1:
                v = v + alphas[t]
        out.append(v)
    return out


def _rw_combine(p, beta):
    def f(v):
        eq, V, I = v[0], v[1], v[2]
        ra = v[3:4 + p]
        phi = v[4 + p:]
        acc = K.ZERO
        for x in range(p + 1):
            acc = acc + beta[x] * ra[x] * (V + phi[x])
        acc = acc + beta[p] * ra[p] * I
        return eq * acc
    return f


def _mul3(v):
    return v[0] * v[1] * v[2]


def _mul2(v):
    return v[0] * v[1]


def _k_rows(full: list, NK: int, T: int, r_k: list) -> list:
    """g(j) = sum_k eq(r_k, k) full[k + NK j]."""
    e = eq_table(r_k)
    out = []
    for j in range(T):
        acc = K.ZERO
        for k in range(NK):
            if full[k + NK * j]:
                acc = acc + e[k]
        out.append(acc)
    return out


def _s_out_bits(final: FinalMem, a: int) -> list:
    return [K((final.s_out >> i) & 1) for i in range(a - final.m)]


def _groups(params, final, r_k, r_j, rw_ev, s_v, val_ev, r_kf, s_f, fin_ev):
    p, d = params.p, params.d
    nm = comp_names_tw(params)
    groups = []
    for s in range(p):
        groups.append(VirtGroup(nm[s * d:(s + 1) * d], r_k, [VirtTerm(r_j, rw_ev[s])]))
    groups.append(VirtGroup(nm[p * d:], r_k,
                            [VirtTerm(r_j, rw_ev[p]), VirtTerm(s_v, val_ev[0])]))
    if final is not None:
        groups.append(VirtGroup(nm[p * d:], r_kf, [VirtTerm(s_f, fin_ev[0])]))
    return groups


def twist_prove(params: TwistParams, m0: list, wit: TwistWitness, claims: TwistClaims,
                transcript: Transcript, label: bytes, final: FinalMem | None = None,
                inc_extra: bool = False):
    a, d, p, n, ell = params.a, params.d, params.p, params.n, params.ell
    NK, T, L = 1 << a, 1 << n, 1 << ell
    _absorb(transcript, label, claims)
    alpha0, alphas, beta = _coeffs(transcript, label, p, a)

    fulls = [full_table(wit.ra[s], a, d, T) for s in range(p)] + [full_table(wit.wa, a, d, T)]
    eo = eq_table(claims.r_o)
    # V(k, j) = Val~(k, r_o, j) by replaying the increments; I(j) = Inc~(r_o, j)
    state = list(m0)
    V = [[K.ZERO] * T for _ in range(NK)]
    I = []
    incs = []
    for j in range(T):
        iv = 0
        acc = K.ZERO
        for o in range(L):
            if wit.inc[o + L * j]:
                iv |= 1 << o
                acc = acc + eo[o]
        incs.append(iv)
        I.append(acc)
    for j in range(T):
        for k in range(NK):
            acc = K.ZERO
            sv = state[k]
            for o in range(L):
                if (sv >> o) & 1:
                    acc = acc + eo[o]
            V[k][j] = acc
        for k in range(NK):
            if fulls[p][k + NK * j]:
                state[k] ^= incs[j]
    final_state = state

    def dom(fn):
        return [fn(j, k) for k in range(NK) for j in range(T)]

    eqc = eq_table(claims.r_c)
    tables = [dom(lambda j, k: eqc[j]), dom(lambda j, k: V[k][j]), dom(lambda j, k: I[j])]
    tables += [dom(lambda j, k, x=x: fulls[x][k + NK * j]) for x in range(p + 1)]
    phis = [_phi_k(alpha0[x], alphas[x], a) for x in range(p + 1)]
    tables += [dom(lambda j, k, x=x: phis[x][k]) for x in range(p + 1)]
    f = _rw_combine(p, beta)
    claim = K.ZERO
    for i in range(T * NK):
        claim = claim + f([t[i] for t in tables])
    rw, r, mles = sumcheck_prove(claim, tables, f, 3, transcript, label + b"/rw")
    r_j, r_k = r[:n], r[n:]
    rw_ev = [mles[3 + x] for x in range(p + 1)] + [mles[1], mles[2]]
    transcript.absorb_ks(label + b"/rw/evals", rw_ev)

    # Val evaluation
    wa_r = _k_rows(fulls[p], NK, T, r_k)
    claim = K.ZERO
    lt = lt_table(r_j)
    for j in range(T):
        claim = claim + lt[j] * wa_r[j] * I[j]
    val, s_v, mles = sumcheck_prove(claim, [lt, wa_r, I], _mul3, 3, transcript, label + b"/val")
    val_ev = [mles[1], mles[2]]
    transcript.absorb_ks(label + b"/val/evals", val_ev)

    # final memory
    fin = fin_ev = None
    r_kf = s_f = None
    r_of = None
    if final is not None:
        r_low = transcript.challenge_ks(label + b"/fin/r_low", final.m)
        r_of = transcript.challenge_ks(label + b"/fin/r_o", ell)
        r_kf = r_low + _s_out_bits(final, a)
        eof = eq_table(r_of)
        wa_f = _k_rows(fulls[p], NK, T, r_kf)
        I_f = []
        for j in range(T):
            acc = K.ZERO
            for o in range(L):
                if wit.inc[o + L * j]:
                    acc = acc + eof[o]
            I_f.append(acc)
        claim = K.ZERO
        for j in range(T):
            claim = claim + wa_f[j] * I_f[j]
        fin, s_f, mles = sumcheck_prove(claim, [wa_f, I_f], _mul2, 2, transcript, label + b"/fin")
        fin_ev = [mles[0], mles[1]]
        transcript.absorb_ks(label + b"/fin/evals", fin_ev)

    extra = None
    extra_claim = None
    if inc_extra:
        xo = transcript.challenge_ks(label + b"/incx/o", ell)
        xc = transcript.challenge_ks(label + b"/incx/c", n)
        extra = mle_eval(wit.inc, xo + xc)
        transcript.absorb_k(label + b"/incx/val", extra)
        extra_claim = EvalClaim(f"{params.name}/inc", xo + xc, extra)

    groups = _groups(params, final, r_k, r_j, rw_ev, s_v, val_ev, r_kf, s_f, fin_ev)
    comps_per_group = [wit.ra[s] for s in range(p)] + [wit.wa] + ([wit.wa] if final else [])
    vproof, vclaims = virt_prove(groups, comps_per_group, a, d, n, transcript, label + b"/virt")
    all_comps = [c for s in range(p) for c in wit.ra[s]] + list(wit.wa)
    oproof, oclaims = onehot_prove(all_comps, comp_names_tw(params), a // d, n,
                                   transcript, label + b"/onehot")
    inc_claims = _inc_claims(params, claims, r_j, rw_ev, s_v, val_ev, r_of, s_f, fin_ev)
    out = TwistOutput(vclaims + oclaims + inc_claims + ([extra_claim] if extra_claim else []),
                      extra_claim)
    return TwistProof(rw, rw_ev, val, val_ev, fin, fin_ev, extra, vproof, oproof), out


def _inc_claims(params, claims, r_j, rw_ev, s_v, val_ev, r_of, s_f, fin_ev):
    nm = f"{params.name}/inc"
    out = [EvalClaim(nm, claims.r_o + r_j, rw_ev[-1]),
           EvalClaim(nm, claims.r_o + s_v, val_ev[1])]
    if fin_ev is not None:
        out.append(EvalClaim(nm, r_of + s_f, fin_ev[1]))
    return out


def twist_verify(params: TwistParams, m0_eval, claims: TwistClaims, proof: TwistProof,
                 transcript: Transcript, label: bytes, final: FinalMem | None = None,
                 inc_extra: bool = False) -> TwistOutput:
    """m0_eval(point) must return M0~(point) for point = r_k || r_o (a + ell coordinates)."""
    a, d, p, n, ell = params.a, params.d, params.p, params.n, params.ell
    if (len(claims.rv) != p or len(claims.bits) != p + 1 or len(claims.r_o) != ell
            or len(claims.r_c) != n or any(len(b) != a for b in claims.bits)):
        raise VerificationError("twist: malformed claims")
    if len(proof.rw_evals) != p + 3 or len(proof.val_evals) != 2:
        raise VerificationError("twist: malformed proof")
    if (final is None) != (proof.fin is None) or (inc_extra != (proof.inc_extra is not None)):
        raise VerificationError("twist: proof shape does not match instance")
    _absorb(transcript, label, claims)
    alpha0, alphas, beta = _coeffs(transcript, label, p, a)
    claim = K.ZERO
    for x in range(p + 1):
        v = claims.rv[x] if x < p else claims.wv
        t = v + alpha0[x]
        for al, f in zip(alphas[x], claims.bits[x]):
            t = t + al * f
        claim = claim + beta[x] * t
    r, expected = sumcheck_verify(claim, n + a, 3, proof.rw, transcript, label + b"/rw")
    r_j, r_k = r[:n], r[n:]
    ev = proof.rw_evals
    transcript.absorb_ks(label + b"/rw/evals", ev)
    V, I = ev[p + 1], ev[p + 2]
    acc = K.ZERO
    for x in range(p + 1):
        phi = alpha0[x]
        for al, rk in zip(alphas[x], r_k):
            phi = phi + al * rk
        acc = acc + beta[x] * ev[x] * (V + phi)
    acc = acc + beta[p] * ev[p] * I
    if eq_eval(claims.r_c, r_j) * acc != expected:
        raise VerificationError("twist: read/write check failed")

    claim = V + m0_eval(r_k + claims.r_o)
    s_v, expected = sumcheck_verify(claim, n, 3, proof.val, transcript, label + b"/val")
    transcript.absorb_ks(label + b"/val/evals", proof.val_evals)
    if lt_eval(s_v, r_j) * proof.val_evals[0] * proof.val_evals[1] != expected:
        raise VerificationError("twist: val check failed")

    r_kf = s_f = r_of = None
    fin_ev = None
    if final is not None:
        if len(final.words) != 1 << final.m or not 0 <= final.s_out < 1 << (a - final.m):
            raise VerificationError("twist: bad final-memory spec")
        r_low = transcript.challenge_ks(label + b"/fin/r_low", final.m)
        r_of = transcript.challenge_ks(label + b"/fin/r_o", ell)
        r_kf = r_low + _s_out_bits(final, a)
        claim = mle_eval(out_table(final.words, ell), r_low + r_of) + m0_eval(r_kf + r_of)
        s_f, expected = sumcheck_verify(claim, n, 2, proof.fin, transcript, label + b"/fin")
        fin_ev = proof.fin_evals
        if len(fin_ev) != 2:
            raise VerificationError("twist: malformed final evals")
        transcript.absorb_ks(label + b"/fin/evals", fin_ev)
        if fin_ev[0] * fin_ev[1] != expected:
            raise VerificationError("twist: final-memory check failed")

    extra_claim = None
    if inc_extra:
        xo = transcript.challenge_ks(label + b"/incx/o", ell)
        xc = transcript.challenge_ks(label + b"/incx/c", n)
        transcript.absorb_k(label + b"/incx/val", proof.inc_extra)
        extra_claim = EvalClaim(f"{params.name}/inc", xo + xc, proof.inc_extra)

    groups = _groups(params, final, r_k, r_j, ev, s_v, proof.val_evals, r_kf, s_f, fin_ev)
    vclaims = virt_verify(groups, a, d, n, proof.virt, transcript, label + b"/virt")
    oclaims = onehot_verify(comp_names_tw(params), a // d, n, proof.onehot, transcript,
                            label + b"/onehot")
    inc_claims = _inc_claims(params, claims, r_j, ev, s_v, proof.val_evals, r_of, s_f, fin_ev)
    return TwistOutput(vclaims + oclaims + inc_claims + ([extra_claim] if extra_claim else []),
                       extra_claim)
