"""BinaryRouter (docs/spec/08-router.md): shift and sub-word store instances.

`wbits` is log2 of the word width W.  The specification fixes wbits = 6 (W = 64);
smaller values exist only to keep the pure-Python model fast in tests.  For stores
the offset has `wbits - 3` bits (3 for W = 64).
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from .field import K
from .mle import eq_table, eq_eval
from .onehot import EvalClaim
from .sumcheck import SumcheckProof, sumcheck_prove, sumcheck_verify, VerificationError
from .transcript import Transcript

SLL, SRL, SRA, SLLW, SRLW, SRAW, SEXT32, ZEXT32 = range(8)
KIND_NAMES = ["SLL", "SRL", "SRA", "SLLW", "SRLW", "SRAW", "SEXT32", "ZEXT32"]


# ------------------------------------------------------------------ shifts

def shift_valid(kind: int, amt: int, wbits: int = 6) -> bool:
    W = 1 << wbits
    if kind in (SLL, SRL, SRA):
        return 0 <= amt < W
    if kind in (SLLW, SRLW, SRAW):
        return 0 <= amt < W // 2
    return amt == 0


def shift_source(kind: int, amt: int, o: int, wbits: int = 6):
    """Source bit index feeding output bit o under routing (amt, kind), or None."""
    W = 1 << wbits
    H = W // 2
    if not shift_valid(kind, amt, wbits):
        return None
    if kind == SLL:
        return o - amt if o >= amt else None
    if kind == SRL:
        return o + amt if o + amt < W else None
    if kind == SRA:
        return min(o + amt, W - 1)
    if kind == SLLW:
        if o < H:
            return o - amt if o >= amt else None
        return H - 1 - amt
    if kind == SRLW:
        if o < H:
            return o + amt if o + amt < H else None
        return H - 1 + amt if amt == 0 else None
    if kind == SRAW:
        return min(o + amt, H - 1) if o < H else H - 1
    if kind == SEXT32:
        return o if o < H else H - 1
    if kind == ZEXT32:
        return o if o < H else None
    raise ValueError("bad kind")


@lru_cache(maxsize=None)
def shift_entries(wbits: int = 6) -> tuple:
    """Support of R_sh: tuples (o, u, h) with h = amt + W * kind."""
    W = 1 << wbits
    out = []
    for kind in range(8):
        for amt in range(W):
            for o in range(W):
                u = shift_source(kind, amt, o, wbits)
                if u is not None:
                    out.append((o, u, amt + W * kind))
    return tuple(out)


def apply_shift(kind: int, amt: int, src: int, wbits: int = 6) -> int:
    """Reference semantics with integer arithmetic (independent of shift_source);
    returns 0 for invalid routings."""
    W = 1 << wbits
    H = W // 2
    M, MH = (1 << W) - 1, (1 << H) - 1
    if not shift_valid(kind, amt, wbits):
        return 0

    def sext(x):
        return (x | (M ^ MH)) if (x >> (H - 1)) & 1 else x

    def sgn(x, w):
        return x - (1 << w) if (x >> (w - 1)) & 1 else x
    src &= M
    if kind == SLL:
        return (src << amt) & M
    if kind == SRL:
        return src >> amt
    if kind == SRA:
        return (sgn(src, W) >> amt) & M
    if kind == SLLW:
        return sext(((src << amt)) & MH)
    if kind == SRLW:
        return sext((src & MH) >> amt)
    if kind == SRAW:
        return sext((sgn(src & MH, H) >> amt) & MH)
    if kind == SEXT32:
        return sext(src & MH)
    return src & MH


def shift_R_eval(r_o: list, r_u: list, r_h: list, wbits: int = 6) -> K:
    """R~_sh(r_o, r_u, r_h), r_h = r_hlo || r_hhi (h = amt + W*kind).  O(|supp R|)."""
    eo, eu, eh = eq_table(r_o), eq_table(r_u), eq_table(r_h)
    acc = K.ZERO
    for o, u, h in shift_entries(wbits):
        acc = acc + eo[o] * eu[u] * eh[h]
    return acc


# ------------------------------------------------------------------ stores

def store_valid(h: int, a: int, wbits: int = 6) -> bool:
    nbytes = (1 << wbits) // 8
    w = 1 << h
    return w <= nbytes and a % w == 0 and 0 <= a < nbytes


@lru_cache(maxsize=None)
def store_entries(wbits: int = 6) -> tuple:
    """Support of R_st: tuples (o, u, h, a)."""
    W = 1 << wbits
    out = []
    for h in range(4):
        for a in range(W // 8):
            if not store_valid(h, a, wbits):
                continue
            for b in range(a, a + (1 << h)):
                for i in range(8):
                    o = 8 * b + i
                    out.append((o, o, h, a))
                    out.append((o, W + 8 * (b - a) + i, h, a))
    return tuple(out)


def apply_store(old: int, src: int, h: int, a: int, wbits: int = 6) -> int:
    """Reference increment (old XOR new) for a store; 0 if (h, a) is invalid."""
    if not store_valid(h, a, wbits):
        return 0
    w = 1 << h
    mask = ((1 << (8 * w)) - 1) << (8 * a)
    new = (old & ~mask) | ((src << (8 * a)) & mask)
    return old ^ new


def store_R_eval(r_o: list, r_u: list, r_h: list, r_a: list, wbits: int = 6) -> K:
    """R~_st(r_o, r_u, r_h, r_a): multilinear in the offset arguments r_a."""
    eo, eu, eh = eq_table(r_o), eq_table(r_u), eq_table(r_h)
    ea = eq_table(r_a)
    acc = K.ZERO
    for o, u, h, a in store_entries(wbits):
        acc = acc + eo[o] * eu[u] * eh[h] * ea[a]
    return acc


# ------------------------------------------------------------- witnesses

def shift_witness(cycles: list, wbits: int = 6) -> dict:
    """cycles[j] = (src_word, (amt, kind) or None).  Returns tables X, Qlo, Qhi, Y."""
    W = 1 << wbits
    X, Qlo, Qhi, Y = [], [], [], []
    for src, route in cycles:
        X += [(src >> u) & 1 for u in range(W)]
        lo, hi = [0] * W, [0] * 8
        y = 0
        if route is not None:
            amt, kind = route
            lo[amt] = 1
            hi[kind] = 1
            y = apply_shift(kind, amt, src, wbits)
        Qlo += lo
        Qhi += hi
        Y += [(y >> o) & 1 for o in range(W)]
    return dict(X=X, Qlo=Qlo, Qhi=Qhi, Y=Y)


def store_witness(cycles: list, wbits: int = 6) -> dict:
    """cycles[j] = (old_word, src_word, (h, a) or None).  Tables X, Q, abits, Inc."""
    W, na = 1 << wbits, wbits - 3
    X, Q, Inc = [], [], []
    abits = [[] for _ in range(na)]
    for old, src, route in cycles:
        X += [(old >> u) & 1 for u in range(W)] + [(src >> u) & 1 for u in range(W)]
        q = [0] * 4
        inc, a = 0, 0
        if route is not None:
            h, a = route
            q[h] = 1
            inc = apply_store(old, src, h, a, wbits)
        Q += q
        Inc += [(inc >> o) & 1 for o in range(W)]
        for b in range(na):
            abits[b].append((a >> b) & 1)
    return dict(X=X, Q=Q, abits=abits, Inc=Inc)


# ----------------------------------------------------------- shift protocol

@dataclass
class RouterProof:
    sc: SumcheckProof
    evals: list         # shift: [X~, Qlo~, Qhi~]; store: [X~, Q~, a~_1..a~_na]


def _absorb_claim(tr, label, r_o, r_j, y):
    tr.absorb_ks(label + b"/point_o", r_o)
    tr.absorb_ks(label + b"/point_c", r_j)
    tr.absorb_k(label + b"/y", y)


def shift_prove(n: int, wit: dict, r_o: list, r_j: list, y: K, transcript: Transcript,
                label: bytes, wbits: int = 6):
    T, W = 1 << n, 1 << wbits
    _absorb_claim(transcript, label, r_o, r_j, y)
    eo = eq_table(r_o)
    Rr = [K.ZERO] * (W * 8 * W)          # flat u + W*h
    for o, u, h in shift_entries(wbits):
        Rr[u + W * h] = Rr[u + W * h] + eo[o]
    eqj = eq_table(r_j)
    X, Qlo, Qhi = wit["X"], wit["Qlo"], wit["Qhi"]
    tabs = [[], [], [], [], []]
    for hhi in range(8):
        for hlo in range(W):
            for u in range(W):
                for j in range(T):
                    tabs[0].append(eqj[j])
                    tabs[1].append(X[u + W * j])
                    tabs[2].append(Qlo[hlo + W * j])
                    tabs[3].append(Qhi[hhi + 8 * j])
                    tabs[4].append(Rr[u + W * (hlo + W * hhi)])
    f = _mul5
    claim = K.ZERO
    for i in range(len(tabs[0])):
        claim = claim + f([t[i] for t in tabs])
    sc, r, mles = sumcheck_prove(claim, tabs, f, 4, transcript, label + b"/sc")
    evals = [mles[1], mles[2], mles[3]]
    transcript.absorb_ks(label + b"/evals", evals)
    return RouterProof(sc, evals), _shift_claims(n, wbits, r, evals)


def _mul5(v):
    return v[0] * v[1] * v[2] * v[3] * v[4]


def _shift_claims(n, wbits, r, evals):
    s_j, s_u = r[:n], r[n:n + wbits]
    s_lo, s_hi = r[n + wbits:n + 2 * wbits], r[n + 2 * wbits:]
    return [EvalClaim("shift/src", s_u + s_j, evals[0]),
            EvalClaim("shift/qlo", s_lo + s_j, evals[1]),
            EvalClaim("shift/qhi", s_hi + s_j, evals[2])]


def shift_verify(n: int, r_o: list, r_j: list, y: K, proof: RouterProof,
                 transcript: Transcript, label: bytes, wbits: int = 6) -> list:
    if len(proof.evals) != 3:
        raise VerificationError("shift: malformed evals")
    _absorb_claim(transcript, label, r_o, r_j, y)
    m = n + 2 * wbits + 3
    r, expected = sumcheck_verify(y, m, 4, proof.sc, transcript, label + b"/sc")
    transcript.absorb_ks(label + b"/evals", proof.evals)
    s_j, s_u = r[:n], r[n:n + wbits]
    r_h = r[n + wbits:]
    x, qlo, qhi = proof.evals
    val = eq_eval(r_j, s_j) * x * qlo * qhi * shift_R_eval(r_o, s_u, r_h, wbits)
    if val != expected:
        raise VerificationError("shift: final check failed")
    return _shift_claims(n, wbits, r, proof.evals)


# ----------------------------------------------------------- store protocol

def store_prove(n: int, wit: dict, r_o: list, r_j: list, y: K, transcript: Transcript,
                label: bytes, wbits: int = 6):
    T, W, na = 1 << n, 1 << wbits, wbits - 3
    NA = 1 << na
    _absorb_claim(transcript, label, r_o, r_j, y)
    eo = eq_table(r_o)
    Ra = [[K.ZERO] * (2 * W * 4) for _ in range(NA)]     # flat u + 2W*h per offset a
    for o, u, h, a in store_entries(wbits):
        Ra[a][u + 2 * W * h] = Ra[a][u + 2 * W * h] + eo[o]
    eqj = eq_table(r_j)
    X, Q, ab = wit["X"], wit["Q"], wit["abits"]
    tabs = [[] for _ in range(3 + na + NA)]
    for h in range(4):
        for u in range(2 * W):
            for j in range(T):
                tabs[0].append(eqj[j])
                tabs[1].append(X[u + 2 * W * j])
                tabs[2].append(Q[h + 4 * j])
                for b in range(na):
                    tabs[3 + b].append(ab[b][j])
                for a in range(NA):
                    tabs[3 + na + a].append(Ra[a][u + 2 * W * h])
    f = _store_combine(na)
    claim = K.ZERO
    for i in range(len(tabs[0])):
        claim = claim + f([t[i] for t in tabs])
    sc, r, mles = sumcheck_prove(claim, tabs, f, 3 + na, transcript, label + b"/sc")
    evals = [mles[1], mles[2]] + [mles[3 + b] for b in range(na)]
    transcript.absorb_ks(label + b"/evals", evals)
    return RouterProof(sc, evals), _store_claims(n, wbits, r, evals)


def _store_combine(na):
    NA = 1 << na

    def f(v):
        eq, x, q = v[0], v[1], v[2]
        ab = v[3:3 + na]
        acc = K.ZERO
        for a in range(NA):
            e = v[3 + na + a]
            for b in range(na):
                e = e * (K.ONE + ab[b] + K((a >> b) & 1))
            acc = acc + e
        return eq * x * q * acc
    return f


def _store_claims(n, wbits, r, evals):
    na = wbits - 3
    s_j, s_u, s_h = r[:n], r[n:n + wbits + 1], r[n + wbits + 1:]
    out = [EvalClaim("store/src", s_u + s_j, evals[0]),
           EvalClaim("store/q", s_h + s_j, evals[1])]
    out += [EvalClaim(f"store/a{b}", s_j, evals[2 + b]) for b in range(na)]
    return out


def store_verify(n: int, r_o: list, r_j: list, y: K, proof: RouterProof,
                 transcript: Transcript, label: bytes, wbits: int = 6) -> list:
    na = wbits - 3
    if len(proof.evals) != 2 + na:
        raise VerificationError("store: malformed evals")
    _absorb_claim(transcript, label, r_o, r_j, y)
    m = n + wbits + 1 + 2
    r, expected = sumcheck_verify(y, m, 3 + na, proof.sc, transcript, label + b"/sc")
    transcript.absorb_ks(label + b"/evals", proof.evals)
    s_j, s_u, s_h = r[:n], r[n:n + wbits + 1], r[n + wbits + 1:]
    x, q = proof.evals[0], proof.evals[1]
    a_vals = proof.evals[2:]
    val = eq_eval(r_j, s_j) * x * q * store_R_eval(r_o, s_u, s_h, a_vals, wbits)
    if val != expected:
        raise VerificationError("store: final check failed")
    return _store_claims(n, wbits, r, proof.evals)


# ------------------------------------------------------------------ fast provers
# Same transcript and proof as shift_prove / store_prove (checked by test_protocol.py), but the
# first n rounds (cycle variables) exploit that Q is sparse per cycle, which makes the prover
# practical in pure Python at W = 64.  Informative only; the spec is the dense definition.

def _ks(x):
    return x if isinstance(x, K) else K(int(x))


def _tpt(a: K, b: K, t: K) -> K:
    return a + t * (a + b)


def _dense_rounds(tabs, combine, degree, cur, tr, label, nrounds, rs, msgs):
    """Continue a sum-check (already initialised) for `nrounds` rounds on dense tables."""
    from .mle import bind_low
    from .sumcheck import interpolate_eval
    for _ in range(nrounds):
        half = len(tabs[0]) // 2
        ev = []
        for k in range(degree + 1):
            t = K.t(k)
            acc = K.ZERO
            for i in range(half):
                acc = acc + combine([T[2 * i] + t * (T[2 * i] + T[2 * i + 1]) for T in tabs])
            ev.append(acc)
        if ev[0] + ev[1] != cur:
            raise ValueError("claim inconsistent with tables (g(0)+g(1) != claim)")
        msg = [ev[0]] + ev[2:]
        tr.absorb_ks(label + b"/msg", msg)
        r = tr.challenge_k(label + b"/chal")
        msgs.append(msg)
        rs.append(r)
        cur = interpolate_eval(ev, r)
        tabs = [bind_low(T, r) for T in tabs]
    return tabs


def _sparse_phase(n, state, evals_fn, bind_fn, degree, claim_hint, tr, label, m_total):
    """Run the n cycle rounds. evals_fn(state) -> [g(t_0)..g(t_degree)] (full, incl. t_1)."""
    from .sumcheck import _init, interpolate_eval
    ev = evals_fn(state)
    claim = ev[0] + ev[1]
    _init(tr, label, claim, m_total, degree)
    rs, msgs, cur = [], [], claim
    for i in range(n):
        if i:
            ev = evals_fn(state)
        if ev[0] + ev[1] != cur:
            raise ValueError("claim inconsistent with tables (g(0)+g(1) != claim)")
        msg = [ev[0]] + ev[2:]
        tr.absorb_ks(label + b"/msg", msg)
        r = tr.challenge_k(label + b"/chal")
        msgs.append(msg)
        rs.append(r)
        cur = interpolate_eval(ev, r)
        state = bind_fn(state, r)
    return state, rs, msgs, cur


def shift_prove_fast(n: int, wit: dict, r_o: list, r_j: list, y: K, transcript: Transcript,
                     label: bytes, wbits: int = 6):
    T, W = 1 << n, 1 << wbits
    _absorb_claim(transcript, label, r_o, r_j, y)
    eo = eq_table(r_o)
    Rh: dict[int, dict[int, K]] = {}
    Rr = [K.ZERO] * (W * 8 * W)
    for o, u, h in shift_entries(wbits):
        d = Rh.setdefault(h, {})
        d[u] = d.get(u, K.ZERO) + eo[o]
        Rr[u + W * h] = Rr[u + W * h] + eo[o]
    X, Qlo, Qhi = wit["X"], wit["Qlo"], wit["Qhi"]
    st = dict(eq=eq_table(r_j),
              X=[[K(X[u + W * j]) for j in range(T)] for u in range(W)],
              Ql=[[K(Qlo[h + W * j]) for j in range(T)] for h in range(W)],
              Qh=[[K(Qhi[h + 8 * j]) for j in range(T)] for h in range(8)])
    ts = [K.t(k) for k in range(5)]

    def evals(s):
        half = len(s["eq"]) // 2
        out = [K.ZERO] * 5
        for p in range(half):
            e0, e1 = s["eq"][2 * p], s["eq"][2 * p + 1]
            lo = [h for h in range(W) if s["Ql"][h][2 * p] or s["Ql"][h][2 * p + 1]]
            hi = [h for h in range(8) if s["Qh"][h][2 * p] or s["Qh"][h][2 * p + 1]]
            if not lo or not hi:
                continue
            for k in range(5):
                t = ts[k]
                et = _tpt(e0, e1, t)
                xt = [_tpt(s["X"][u][2 * p], s["X"][u][2 * p + 1], t) for u in range(W)]
                acc = K.ZERO
                for hh in hi:
                    qh = _tpt(s["Qh"][hh][2 * p], s["Qh"][hh][2 * p + 1], t)
                    if not qh:
                        continue
                    inner = K.ZERO
                    for hl in lo:
                        ql = _tpt(s["Ql"][hl][2 * p], s["Ql"][hl][2 * p + 1], t)
                        if not ql:
                            continue
                        b = K.ZERO
                        for u, c in Rh.get(hl + W * hh, {}).items():
                            b = b + xt[u] * c
                        inner = inner + ql * b
                    acc = acc + qh * inner
                out[k] = out[k] + et * acc
        return out

    def bind(s, r):
        f = lambda tb: [_tpt(tb[2 * i], tb[2 * i + 1], r) for i in range(len(tb) // 2)]
        return dict(eq=f(s["eq"]), X=[f(a) for a in s["X"]], Ql=[f(a) for a in s["Ql"]],
                    Qh=[f(a) for a in s["Qh"]])

    m_total = n + 2 * wbits + 3
    st, rs, msgs, cur = _sparse_phase(n, st, evals, bind, 4, None, transcript, label + b"/sc", m_total)
    e = st["eq"][0]
    NR = W * W * 8
    tabs = [[e] * NR,
            [st["X"][i % W][0] for i in range(NR)],
            [st["Ql"][(i // W) % W][0] for i in range(NR)],
            [st["Qh"][i // (W * W)][0] for i in range(NR)],
            Rr]
    fin = _dense_rounds(tabs, _mul5, 4, cur, transcript, label + b"/sc", m_total - n, rs, msgs)
    mles = [t[0] for t in fin]
    evs = [mles[1], mles[2], mles[3]]
    transcript.absorb_ks(label + b"/evals", evs)
    return RouterProof(SumcheckProof(msgs), evs), _shift_claims(n, wbits, rs, evs)


def store_prove_fast(n: int, wit: dict, r_o: list, r_j: list, y: K, transcript: Transcript,
                     label: bytes, wbits: int = 6):
    T, W, na = 1 << n, 1 << wbits, wbits - 3
    NA = 1 << na
    _absorb_claim(transcript, label, r_o, r_j, y)
    eo = eq_table(r_o)
    Rah: dict[tuple, dict[int, K]] = {}
    Ra = [[K.ZERO] * (2 * W * 4) for _ in range(NA)]
    for o, u, h, a in store_entries(wbits):
        d = Rah.setdefault((a, h), {})
        d[u] = d.get(u, K.ZERO) + eo[o]
        Ra[a][u + 2 * W * h] = Ra[a][u + 2 * W * h] + eo[o]
    X, Q, ab = wit["X"], wit["Q"], wit["abits"]
    st = dict(eq=eq_table(r_j),
              X=[[K(X[u + 2 * W * j]) for j in range(T)] for u in range(2 * W)],
              Q=[[K(Q[h + 4 * j]) for j in range(T)] for h in range(4)],
              ab=[[K(ab[b][j]) for j in range(T)] for b in range(na)])
    degree = 3 + na
    ts = [K.t(k) for k in range(degree + 1)]

    def evals(s):
        half = len(s["eq"]) // 2
        out = [K.ZERO] * (degree + 1)
        for p in range(half):
            hs = [h for h in range(4) if s["Q"][h][2 * p] or s["Q"][h][2 * p + 1]]
            if not hs:
                continue
            for k in range(degree + 1):
                t = ts[k]
                et = _tpt(s["eq"][2 * p], s["eq"][2 * p + 1], t)
                xt = [_tpt(s["X"][u][2 * p], s["X"][u][2 * p + 1], t) for u in range(2 * W)]
                abt = [_tpt(s["ab"][b][2 * p], s["ab"][b][2 * p + 1], t) for b in range(na)]
                La = []
                for a in range(NA):
                    v = K.ONE
                    for b in range(na):
                        v = v * (K.ONE + abt[b] + K((a >> b) & 1))
                    La.append(v)
                acc = K.ZERO
                for h in hs:
                    qh = _tpt(s["Q"][h][2 * p], s["Q"][h][2 * p + 1], t)
                    if not qh:
                        continue
                    inner = K.ZERO
                    for a in range(NA):
                        if not La[a]:
                            continue
                        b_ = K.ZERO
                        for u, c in Rah.get((a, h), {}).items():
                            b_ = b_ + xt[u] * c
                        inner = inner + La[a] * b_
                    acc = acc + qh * inner
                out[k] = out[k] + et * acc
        return out

    def bind(s, r):
        f = lambda tb: [_tpt(tb[2 * i], tb[2 * i + 1], r) for i in range(len(tb) // 2)]
        return dict(eq=f(s["eq"]), X=[f(a) for a in s["X"]], Q=[f(a) for a in s["Q"]],
                    ab=[f(a) for a in s["ab"]])

    m_total = n + wbits + 1 + 2
    st, rs, msgs, cur = _sparse_phase(n, st, evals, bind, degree, None, transcript, label + b"/sc", m_total)
    NR = 2 * W * 4
    tabs = [[st["eq"][0]] * NR,
            [st["X"][i % (2 * W)][0] for i in range(NR)],
            [st["Q"][i // (2 * W)][0] for i in range(NR)]]
    tabs += [[st["ab"][b][0]] * NR for b in range(na)]
    tabs += [Ra[a] for a in range(NA)]
    fin = _dense_rounds(tabs, _store_combine(na), degree, cur, transcript, label + b"/sc",
                        m_total - n, rs, msgs)
    mles = [t[0] for t in fin]
    evs = [mles[1], mles[2]] + [mles[3 + b] for b in range(na)]
    transcript.absorb_ks(label + b"/evals", evs)
    return RouterProof(SumcheckProof(msgs), evs), _store_claims(n, wbits, rs, evs)
