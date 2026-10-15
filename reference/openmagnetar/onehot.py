"""Address decomposition, the Frobenius one-hot check (Delta-star) and address
virtualization.  Spec: docs/spec/07-twist-shout.md sections 7.1 to 7.3.

Conventions (CONVENTIONS C2): a component table A_i has index u + 2^ac * j
(address chunk u in the LOW bits, cycle j in the high bits).  Component 1 holds
the lowest ac bits of the address.  Points are lists of K, x_1 first.
"""

from __future__ import annotations

from dataclasses import dataclass

from .field import K
from .mle import eq_table, eq_eval
from .sumcheck import SumcheckProof, sumcheck_prove, sumcheck_verify, VerificationError
from .transcript import Transcript


@dataclass
class EvalClaim:
    """An evaluation claim on a committed polynomial: poly~(point) = value."""
    poly: str
    point: list
    value: K


def bits_of(x: int, n: int) -> list:
    return [K((x >> i) & 1) for i in range(n)]


# ---------------------------------------------------------------- addresses

def split_addr(addr: int, a: int, d: int) -> list:
    """Chunks of an address; chunk 0 (component 1) is the lowest a/d bits."""
    ac = a // d
    return [(addr >> (i * ac)) & ((1 << ac) - 1) for i in range(d)]


def comp_tables(addrs: list, a: int, d: int) -> list:
    """d flat 0/1 tables, each of length 2^ac * T, index u + 2^ac * j."""
    assert a % d == 0 and a >= d
    ac, T = a // d, len(addrs)
    out = [[0] * ((1 << ac) * T) for _ in range(d)]
    for j, ad in enumerate(addrs):
        for i, ch in enumerate(split_addr(ad, a, d)):
            out[i][ch + (1 << ac) * j] = 1
    return out


def full_table(comps: list, a: int, d: int, T: int) -> list:
    """The virtual full-address table ra(k, j) = prod_i A_i(k^(i), j),
    flat index k + 2^a * j.  Works for arbitrary (also non-one-hot) bit tables."""
    ac, NK = a // d, 1 << a
    out = [0] * (NK * T)
    for j in range(T):
        for k in range(NK):
            v = 1
            for i, ch in enumerate(split_addr(k, a, d)):
                v &= comps[i][ch + (1 << ac) * j]
                if not v:
                    break
            out[k + NK * j] = v
    return out


def split_point(r_k: list, a: int, d: int) -> list:
    ac = a // d
    return [r_k[i * ac:(i + 1) * ac] for i in range(d)]


def partial_eval_rows(table: list, ac: int, T: int, r: list) -> list:
    """g(j) = sum_u eq(r, u) * table[u + 2^ac j]  (MLE in the u variables only)."""
    e = eq_table(r)
    nu = 1 << ac
    out = []
    for j in range(T):
        acc = K.ZERO
        for u in range(nu):
            if table[u + nu * j]:
                acc = acc + e[u]
        out.append(acc)
    return out


# ------------------------------------------------------------ one-hot check

def onehot_aux(r: list):
    """Returns (r', C) or None if some c_h = 1 + r_h + r_h^2 is zero."""
    rp, C = [], K.ONE
    for rh in r:
        c = K.ONE + rh + rh * rh
        if not c:
            return None
        rp.append(rh * rh * rh / c)
        C = C * c
    return rp, C


def sample_onehot_point(transcript: Transcript, label: bytes, ac: int):
    """Draw r in K^ac (all coordinates in one call), retrying the whole draw
    while some c_h = 0."""
    while True:
        r = transcript.challenge_ks(label + b"/r", ac)
        aux = onehot_aux(r)
        if aux is not None:
            return r, aux[0], aux[1]


@dataclass
class OneHotProof:
    sc: SumcheckProof
    evals: list          # per component: [A~(r, s), A~(r', s)]


def _onehot_combine(lam: list, C: K):
    nc = len(lam)

    def f(v):
        acc = K.ZERO
        for x in range(nc):
            xv, yv = v[1 + 2 * x], v[2 + 2 * x]
            acc = acc + lam[x] * (xv * xv * xv + C * yv)
        return v[0] * acc
    return f


def onehot_prove(comps: list, names: list, ac: int, n: int,
                 transcript: Transcript, label: bytes):
    T = 1 << n
    r, rp, C = sample_onehot_point(transcript, label, ac)
    rho = transcript.challenge_ks(label + b"/rho", n)
    lam = transcript.challenge_ks(label + b"/lambda", len(comps))
    tables = [eq_table(rho)]
    for A in comps:
        tables.append(partial_eval_rows(A, ac, T, r))
        tables.append(partial_eval_rows(A, ac, T, rp))
    f = _onehot_combine(lam, C)
    claim = K.ZERO
    for j in range(T):
        claim = claim + f([t[j] for t in tables])
    sc, s, mles = sumcheck_prove(claim, tables, f, 4, transcript, label + b"/sc")
    evals = [[mles[1 + 2 * x], mles[2 + 2 * x]] for x in range(len(comps))]
    transcript.absorb_ks(label + b"/evals", [v for e in evals for v in e])
    claims = []
    for x, nm in enumerate(names):
        claims.append(EvalClaim(nm, r + s, evals[x][0]))
        claims.append(EvalClaim(nm, rp + s, evals[x][1]))
    return OneHotProof(sc, evals), claims


def onehot_verify(names: list, ac: int, n: int, proof: OneHotProof,
                  transcript: Transcript, label: bytes) -> list:
    r, rp, C = sample_onehot_point(transcript, label, ac)
    rho = transcript.challenge_ks(label + b"/rho", n)
    lam = transcript.challenge_ks(label + b"/lambda", len(names))
    s, expected = sumcheck_verify(K.ZERO, n, 4, proof.sc, transcript, label + b"/sc")
    if len(proof.evals) != len(names) or any(len(e) != 2 for e in proof.evals):
        raise VerificationError("onehot: malformed evals")
    transcript.absorb_ks(label + b"/evals", [v for e in proof.evals for v in e])
    acc = K.ZERO
    for x in range(len(names)):
        xv, yv = proof.evals[x]
        acc = acc + lam[x] * (xv * xv * xv + C * yv)
    if eq_eval(rho, s) * acc != expected:
        raise VerificationError("onehot: final check failed")
    claims = []
    for x, nm in enumerate(names):
        claims.append(EvalClaim(nm, r + s, proof.evals[x][0]))
        claims.append(EvalClaim(nm, rp + s, proof.evals[x][1]))
    return claims


# ------------------------------------------------------ address virtualization

@dataclass
class VirtTerm:
    cyc: list           # cycle point c in K^n
    value: K            # claimed ra~(r_k || c)


@dataclass
class VirtGroup:
    names: list         # d polynomial names, component 1 first
    r_k: list           # K^a, the address point
    terms: list         # list[VirtTerm]


@dataclass
class VirtProof:
    sc: SumcheckProof
    evals: list         # per group, per component (flattened group-major)


def virt_prove(groups: list, comps_per_group: list, a: int, d: int, n: int,
               transcript: Transcript, label: bytes):
    """Reduces the claims ra~(r_k || c_t) = v_t to component claims.
    For d = 1 nothing is proven: each term already is a component claim."""
    if d == 1:
        return None, _virt_direct(groups)
    T, ac = 1 << n, a // d
    terms = [(gi, t) for gi, g in enumerate(groups) for t in g.terms]
    nu = transcript.challenge_ks(label + b"/nu", len(terms))
    tables = [eq_table(t.cyc) for _, t in terms]
    base = len(tables)
    for gi, g in enumerate(groups):
        for i, rc in enumerate(split_point(g.r_k, a, d)):
            tables.append(partial_eval_rows(comps_per_group[gi][i], ac, T, rc))
    f = _virt_combine(groups, nu, d)
    # The honest prover sums the actual tables (not the claimed value).
    claim = K.ZERO
    for j in range(T):
        claim = claim + f([t[j] for t in tables])
    sc, s, mles = sumcheck_prove(claim, tables, f, d + 1, transcript, label + b"/sc")
    evals = mles[base:]
    transcript.absorb_ks(label + b"/evals", evals)
    return VirtProof(sc, evals), _virt_claims(groups, d, s, evals, a)


def _virt_combine(groups, nu, d):
    # table layout: one eq table per term (group-major), then d tables per group
    nterms = sum(len(g.terms) for g in groups)

    def f(v):
        acc, tpos = K.ZERO, 0
        for gi, g in enumerate(groups):
            coef = K.ZERO
            for _ in g.terms:
                coef = coef + nu[tpos] * v[tpos]
                tpos += 1
            prod = coef
            for i in range(d):
                prod = prod * v[nterms + gi * d + i]
            acc = acc + prod
        return acc
    return f


def _virt_direct(groups):
    return [EvalClaim(g.names[0], g.r_k + t.cyc, t.value) for g in groups for t in g.terms]


def _virt_claims(groups, d, s, evals, a):
    out = []
    for gi, g in enumerate(groups):
        for i, rc in enumerate(split_point(g.r_k, a, d)):
            out.append(EvalClaim(g.names[i], rc + s, evals[gi * d + i]))
    return out


def virt_verify(groups: list, a: int, d: int, n: int, proof, transcript: Transcript,
                label: bytes) -> list:
    if d == 1:
        return _virt_direct(groups)
    terms = [(gi, t) for gi, g in enumerate(groups) for t in g.terms]
    nu = transcript.challenge_ks(label + b"/nu", len(terms))
    claim = K.ZERO
    for c, (_, t) in zip(nu, terms):
        claim = claim + c * t.value
    s, expected = sumcheck_verify(claim, n, d + 1, proof.sc, transcript, label + b"/sc")
    if len(proof.evals) != len(groups) * d:
        raise VerificationError("virt: wrong number of evals")
    transcript.absorb_ks(label + b"/evals", proof.evals)
    acc, tpos = K.ZERO, 0
    for gi, g in enumerate(groups):
        coef = K.ZERO
        for t in g.terms:
            coef = coef + nu[tpos] * eq_eval(t.cyc, s)
            tpos += 1
        prod = coef
        for i in range(d):
            prod = prod * proof.evals[gi * d + i]
        acc = acc + prod
    if acc != expected:
        raise VerificationError("virt: final check failed")
    return _virt_claims(groups, d, s, proof.evals, a)
