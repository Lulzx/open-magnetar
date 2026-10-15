"""BinaryShout (docs/spec/07-twist-shout.md section 7.4)."""

from __future__ import annotations

from dataclasses import dataclass

from .field import K
from .mle import eq_table, eq_eval, mle_eval
from .onehot import (EvalClaim, OneHotProof, VirtGroup, VirtProof, VirtTerm, full_table,
                     onehot_prove, onehot_verify, virt_prove, virt_verify)
from .sumcheck import SumcheckProof, sumcheck_prove, sumcheck_verify, VerificationError
from .transcript import Transcript


@dataclass
class ShoutParams:
    name: str
    a: int      # K = 2^a table rows
    d: int      # number of address components, d | a
    n: int      # T = 2^n cycles


@dataclass
class ShoutClaims:
    """One claim group: all claims at one cycle point r_c."""
    r_c: list           # cycle point, K^n
    cols: list          # indices of the table columns claimed (increasing)
    rv: list            # rv_h~(r_c) for h in cols
    bits: list | None   # f_t~(r_c), t = 0..a-1 (t = 0 is the LSB), or None


@dataclass
class ShoutProof:
    read: SumcheckProof
    ra_evals: list
    virt: VirtProof | None
    onehot: OneHotProof


def comp_names(params: ShoutParams) -> list:
    return [f"{params.name}/ra/{i + 1}" for i in range(params.d)]


def _ra_at(params, comps, r_c):
    """ra~(k, r_c) for all Boolean k (length 2^a)."""
    a, n = params.a, params.n
    NK, T = 1 << a, 1 << n
    full = full_table(comps, a, params.d, T)
    e = eq_table(r_c)
    out = []
    for k in range(NK):
        acc = K.ZERO
        for j in range(T):
            if full[k + NK * j]:
                acc = acc + e[j]
        out.append(acc)
    return out


def shout_honest_claims(params: ShoutParams, table: list, comps: list, r_c: list,
                        cols: list | None = None, with_bits: bool = True) -> ShoutClaims:
    cols = list(range(len(table))) if cols is None else list(cols)
    ra = _ra_at(params, comps, r_c)
    rv = []
    for h in cols:
        acc = K.ZERO
        for k, v in enumerate(ra):
            acc = acc + v * table[h][k]
        rv.append(acc)
    bits = None
    if with_bits:
        bits = []
        for t in range(params.a):
            acc = K.ZERO
            for k, v in enumerate(ra):
                if (k >> t) & 1:
                    acc = acc + v
            bits.append(acc)
    return ShoutClaims(list(r_c), cols, rv, bits)


def _phi_table(alpha0, alphas, gammas, table, cols, a) -> list:
    out = []
    for k in range(1 << a):
        v = alpha0
        if alphas is not None:
            for t in range(a):
                if (k >> t) & 1:
                    v = v + alphas[t]
        for g, h in zip(gammas, cols):
            v = v + g * table[h][k]
        out.append(v)
    return out


def _absorb(tr, label, groups):
    tr.absorb_bytes(label + b"/ngroups", len(groups).to_bytes(8, "little"))
    for g in groups:
        tr.absorb_ks(label + b"/point", g.r_c)
        tr.absorb_bytes(label + b"/cols", b"".join(h.to_bytes(8, "little") for h in g.cols)
                        + (b"\x01" if g.bits is not None else b"\x00"))
        tr.absorb_ks(label + b"/rv", g.rv)
        if g.bits is not None:
            tr.absorb_ks(label + b"/bits", g.bits)


def _coeffs(tr, label, a, groups):
    out = []
    for g in groups:
        alpha0 = tr.challenge_nonzero_k(label + b"/alpha0")
        alphas = tr.challenge_ks(label + b"/alpha", a) if g.bits is not None else None
        gammas = tr.challenge_ks(label + b"/gamma", len(g.cols))
        out.append((alpha0, alphas, gammas))
    beta = tr.challenge_ks(label + b"/beta", len(groups))
    return out, beta


def _group_claim(g, co):
    alpha0, alphas, gammas = co
    c = alpha0
    if alphas is not None:
        for al, f in zip(alphas, g.bits):
            c = c + al * f
    for ga, v in zip(gammas, g.rv):
        c = c + ga * v
    return c


def _shout_combine(beta):
    G = len(beta)

    def f(v):
        acc = K.ZERO
        for g in range(G):
            acc = acc + beta[g] * v[g] * v[G + g]
        return acc
    return f


def shout_prove(params: ShoutParams, table: list, comps: list, groups: list,
                transcript: Transcript, label: bytes):
    a, d, n = params.a, params.d, params.n
    _absorb(transcript, label, groups)
    cos, beta = _coeffs(transcript, label, a, groups)
    ra_rs = [_ra_at(params, comps, g.r_c) for g in groups]
    phis = [_phi_table(co[0], co[1], co[2], table, g.cols, a) for g, co in zip(groups, cos)]
    f = _shout_combine(beta)
    tables = ra_rs + phis
    claim = K.ZERO
    for k in range(1 << a):
        claim = claim + f([t[k] for t in tables])
    sc, r_k, mles = sumcheck_prove(claim, tables, f, 2, transcript, label + b"/read")
    ra_evals = mles[:len(groups)]
    transcript.absorb_ks(label + b"/ra_evals", ra_evals)
    names = comp_names(params)
    grp = VirtGroup(names, r_k, [VirtTerm(g.r_c, v) for g, v in zip(groups, ra_evals)])
    vproof, vclaims = virt_prove([grp], [comps], a, d, n, transcript, label + b"/virt")
    oproof, oclaims = onehot_prove(comps, names, a // d, n, transcript, label + b"/onehot")
    return ShoutProof(sc, ra_evals, vproof, oproof), vclaims + oclaims


def shout_verify(params: ShoutParams, table: list, groups: list, proof: ShoutProof,
                 transcript: Transcript, label: bytes) -> list:
    """`table` is the public table: c columns of 2^a field elements."""
    a, d, n = params.a, params.d, params.n
    for g in groups:
        if (len(g.r_c) != n or len(g.rv) != len(g.cols)
                or (g.bits is not None and len(g.bits) != a)
                or any(not 0 <= h < len(table) for h in g.cols)):
            raise VerificationError("shout: malformed claims")
    if len(proof.ra_evals) != len(groups):
        raise VerificationError("shout: malformed proof")
    _absorb(transcript, label, groups)
    cos, beta = _coeffs(transcript, label, a, groups)
    claim = K.ZERO
    for b, g, co in zip(beta, groups, cos):
        claim = claim + b * _group_claim(g, co)
    r_k, expected = sumcheck_verify(claim, a, 2, proof.read, transcript, label + b"/read")
    val = K.ZERO
    for b, g, co, ra in zip(beta, groups, cos, proof.ra_evals):
        alpha0, alphas, gammas = co
        phi = alpha0
        if alphas is not None:
            for al, x in zip(alphas, r_k):
                phi = phi + al * x
        for ga, h in zip(gammas, g.cols):
            phi = phi + ga * mle_eval(table[h], r_k)
        val = val + b * ra * phi
    if val != expected:
        raise VerificationError("shout: read check failed")
    transcript.absorb_ks(label + b"/ra_evals", proof.ra_evals)
    names = comp_names(params)
    grp = VirtGroup(names, r_k, [VirtTerm(g.r_c, v) for g, v in zip(groups, proof.ra_evals)])
    vclaims = virt_verify([grp], a, d, n, proof.virt, transcript, label + b"/virt")
    oclaims = onehot_verify(names, a // d, n, proof.onehot, transcript, label + b"/onehot")
    return vclaims + oclaims
