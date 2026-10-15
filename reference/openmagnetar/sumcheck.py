"""Sum-check per docs/spec/03-sumcheck.md and CONVENTIONS C3."""

from __future__ import annotations

from dataclasses import dataclass

from .field import K
from .mle import bind_low
from .transcript import Transcript


class VerificationError(Exception):
    pass


@dataclass
class SumcheckProof:
    round_msgs: list[list[K]]  # per round: [g(t_0), g(t_2), ..., g(t_d)]


def _u64(n: int) -> bytes:
    return n.to_bytes(8, "little")


def _init(transcript: Transcript, label: bytes, claim: K, m: int, d: int) -> None:
    transcript.absorb_k(label + b"/claim", claim)
    transcript.absorb_bytes(label + b"/params", _u64(m) + _u64(d))


def interpolate_eval(ys: list[K], r: K) -> K:
    """Evaluate at r the unique poly of degree < len(ys) with value ys[k] at t_k."""
    n = len(ys)
    ts = [K.t(k) for k in range(n)]
    acc = K.ZERO
    for k in range(n):
        num, den = K.ONE, K.ONE
        for j in range(n):
            if j != k:
                num = num * (r + ts[j])
                den = den * (ts[k] + ts[j])
        acc = acc + ys[k] * num / den
    return acc


def sumcheck_prove(claim: K, tables: list[list[K]], combine, degree: int,
                   transcript: Transcript, label: bytes
                   ) -> tuple[SumcheckProof, list[K], list[K]]:
    if degree < 1:
        raise ValueError("degree must be >= 1")
    size = len(tables[0])
    if size == 0 or size & (size - 1) or any(len(t) != size for t in tables):
        raise ValueError("tables must share a power-of-two length")
    m = size.bit_length() - 1
    tables = [[x if isinstance(x, K) else K(int(x)) for x in t] for t in tables]
    _init(transcript, label, claim, m, degree)
    msgs, rs = [], []
    cur = claim
    for _ in range(m):
        half = len(tables[0]) // 2
        # evaluations of g at t_0, t_1 (check only), t_2..t_degree
        ev = {}
        for k in range(degree + 1):
            t = K.t(k)
            acc = K.ZERO
            for i in range(half):
                vals = []
                for T in tables:
                    a, b = T[2 * i], T[2 * i + 1]
                    vals.append(a + t * (a + b))
                acc = acc + combine(vals)
            ev[k] = acc
        if ev[0] + ev[1] != cur:
            raise ValueError("claim inconsistent with tables (g(0)+g(1) != claim)")
        msg = [ev[0]] + [ev[k] for k in range(2, degree + 1)]
        transcript.absorb_ks(label + b"/msg", msg)
        r = transcript.challenge_k(label + b"/chal")
        msgs.append(msg)
        rs.append(r)
        cur = interpolate_eval([ev[k] for k in range(degree + 1)], r)
        tables = [bind_low(T, r) for T in tables]
    return SumcheckProof(msgs), rs, [T[0] for T in tables]


def sumcheck_verify(claim: K, num_vars: int, degree: int, proof: SumcheckProof,
                    transcript: Transcript, label: bytes) -> tuple[list[K], K]:
    if degree < 1:
        raise ValueError("degree must be >= 1")
    if len(proof.round_msgs) != num_vars:
        raise VerificationError("wrong number of rounds")
    _init(transcript, label, claim, num_vars, degree)
    rs, cur = [], claim
    for msg in proof.round_msgs:
        if len(msg) != degree or not all(isinstance(x, K) for x in msg):
            raise VerificationError("malformed round message")
        transcript.absorb_ks(label + b"/msg", msg)
        r = transcript.challenge_k(label + b"/chal")
        ys = [msg[0], cur + msg[0]] + list(msg[1:])
        cur = interpolate_eval(ys, r)
        rs.append(r)
    return rs, cur


def batch_claims(claims: list[K], transcript: Transcript, label: bytes) -> tuple[list[K], K]:
    """Random-linear-combination batching of equal-num_vars claims.
    Returns (coeffs [1, g, g^2, ...], combined claim sum_i g^i claim_i)."""
    transcript.absorb_ks(label + b"/claims", claims)
    gamma = transcript.challenge_k(label + b"/gamma")
    coeffs, p = [], K.ONE
    for _ in claims:
        coeffs.append(p)
        p = p * gamma
    combined = K.ZERO
    for c, x in zip(coeffs, claims):
        combined = combined + c * x
    return coeffs, combined


def batched_combine(coeffs: list[K], combines: list, arities: list[int]):
    """Build a single combine over the concatenated table list."""
    def f(vals):
        out, pos = K.ZERO, 0
        for c, fn, a in zip(coeffs, combines, arities):
            out = out + c * fn(vals[pos:pos + a])
            pos += a
        return out
    return f
