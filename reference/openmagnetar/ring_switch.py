"""Ring switching (Diamond-Posen) for the monomial packing basis beta_j = X^j.
Normative description: docs/spec/04-pcs.md section 4.5.

Reduces  MLE(w)(r) = y  for a bit vector w of length 2^ell  (ell >= 8)
to       MLE(P)(r_s) = v  for the packed vector P of length 2^(ell-7).
"""

from __future__ import annotations

from dataclasses import dataclass

from .field import K
from .mle import eq_table, mle_eval
from .sumcheck import (SumcheckProof, VerificationError, sumcheck_prove,
                       sumcheck_verify)
from .transcript import Transcript

KAPPA = 7
W = 1 << KAPPA  # 128


@dataclass
class RingSwitchProof:
    s: list[K]               # 128 partial evaluations s_j
    sumcheck: SumcheckProof  # ell-7 rounds, degree 2


def pack(bits: list[int]) -> list[K]:
    """P[v] = sum_j X^j * bits[j + 128 v]."""
    if len(bits) % W:
        raise ValueError("bit vector length must be a multiple of 128")
    return [K.pack(bits[v * W:(v + 1) * W]) for v in range(len(bits) // W)]


def partial_evals(bits: list[int], r_hi: list[K]) -> list[K]:
    """s_j = sum_v eq(r_hi, v) * bits[j + 128 v]."""
    eqt = eq_table(r_hi)
    s = []
    for j in range(W):
        acc = 0
        for v, e in enumerate(eqt):
            if bits[j + W * v]:
                acc ^= e.v
        s.append(K(acc))
    return s


def transpose_bits(s: list[K]) -> list[K]:
    """c_i = pack_j(bit_i(s_j))  (left coordinates -> right coordinates in K (x)_B K)."""
    return [K(sum(((s[j].v >> i) & 1) << j for j in range(W))) for i in range(W)]


def a_table(r_hi: list[K], rho: list[K]) -> list[K]:
    """a[v] = sum_i eq(rho, i) * bit_i(eq(r_hi, v))."""
    er = [e.v for e in eq_table(rho)]
    out = []
    for e in eq_table(r_hi):
        acc, x, i = 0, e.v, 0
        while x:
            if x & 1:
                acc ^= er[i]
            x >>= 1
            i += 1
        out.append(K(acc))
    return out


def _mul_tensor(t: list[K], x: K, y: K) -> list[K]:
    """T <- T * (x (x) y) with T = sum_i beta_i (x) t_i."""
    acc = [0] * W
    for i in range(W):
        if not t[i].v:
            continue
        xb = (x * K(1 << i)).v
        m = 0
        while xb:
            if xb & 1:
                acc[m] ^= t[i].v
            xb >>= 1
            m += 1
    return [K(a) * y for a in acc]


def a_eval(r_hi: list[K], rho: list[K], z: list[K]) -> K:
    """MLE of a at z, via the tensor algebra  T = prod_k [(1+r_k)(x)(1+z_k) + r_k(x)z_k]."""
    t = [K.ONE] + [K.ZERO] * (W - 1)
    for rk, zk in zip(r_hi, z):
        t1 = _mul_tensor(t, K.ONE + rk, K.ONE + zk)
        t2 = _mul_tensor(t, rk, zk)
        t = [p + q for p, q in zip(t1, t2)]
    er = eq_table(rho)
    acc = K.ZERO
    for i in range(W):
        acc = acc + er[i] * t[i]
    return acc


def _absorb_claim(tr: Transcript, r: list[K], y: K) -> None:
    tr.absorb_ks(b"rs/point", r)
    tr.absorb_k(b"rs/value", y)


def rs_prove(bits: list[int], r: list[K], y: K, tr: Transcript):
    """Returns (proof, r_s, v) with v = MLE(P)(r_s). Caller then proves it with the PCS."""
    ell = len(r)
    if ell < KAPPA + 1 or len(bits) != 1 << ell:
        raise ValueError("need ell >= 8 and 2^ell bits")
    P = pack(bits)
    s = partial_evals(bits, r[KAPPA:])
    _absorb_claim(tr, r, y)
    tr.absorb_ks(b"rs/s", s)
    rho = tr.challenge_ks(b"rs/rho", KAPPA)
    c = transpose_bits(s)
    er = eq_table(rho)
    target = K.ZERO
    for i in range(W):
        target = target + er[i] * c[i]
    a = a_table(r[KAPPA:], rho)
    proof, r_s, finals = sumcheck_prove(target, [P, a], lambda v: v[0] * v[1], 2, tr, b"rs/sumcheck")
    return RingSwitchProof(s, proof), r_s, finals[0]


def rs_verify(r: list[K], y: K, proof: RingSwitchProof, tr: Transcript) -> tuple[list[K], K]:
    """Returns (r_s, v): the PCS must now certify MLE(P)(r_s) = v."""
    ell = len(r)
    if ell < KAPPA + 1:
        raise VerificationError("ell too small")
    if len(proof.s) != W:
        raise VerificationError("s must have 128 entries")
    _absorb_claim(tr, r, y)
    # check 1: sum_j eq(r_lo, j) s_j = y
    e_lo = eq_table(r[:KAPPA])
    acc = K.ZERO
    for e, sj in zip(e_lo, proof.s):
        acc = acc + e * sj
    if acc != y:
        raise VerificationError("ring switching: s inconsistent with claimed value")
    tr.absorb_ks(b"rs/s", proof.s)
    rho = tr.challenge_ks(b"rs/rho", KAPPA)
    c = transpose_bits(proof.s)
    er = eq_table(rho)
    target = K.ZERO
    for i in range(W):
        target = target + er[i] * c[i]
    r_s, final = sumcheck_verify(target, ell - KAPPA, 2, proof.sumcheck, tr, b"rs/sumcheck")
    a_val = a_eval(r[KAPPA:], rho, r_s)
    if not a_val:
        raise VerificationError("ring switching: degenerate a(r_s) = 0")
    return r_s, final / a_val
