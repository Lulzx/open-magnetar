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
    Returns (coeffs [1, g, g^2, ...], combined claim sum_i g^i claim_i).
    At most 256 claims (spec 03.6: (n-1)/|K| < 2^-120 only up to n = 256)."""
    if len(claims) > 256:
        raise ValueError("powers-of-gamma batching is limited to 256 claims (03.6)")
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


@dataclass
class UnivariateSkipProof:
    skip_msg: list[K]
    round_msgs: list[list[K]]


def lagrange_subspace_weights(k: int, z: K) -> list[K]:
    """Lagrange basis weights [L_0(z), ..., L_{2^k - 1}(z)] on D = {t_0, ..., t_{2^k - 1}} (spec 03.9)."""
    if k < 1 or k > 16:
        raise ValueError("skip parameter k must be in 1..16")
    dom = 1 << k
    ts = [K.t(a) for a in range(dom)]
    for b, tb in enumerate(ts):
        if z == tb:
            out = [K.ZERO] * dom
            out[b] = K.ONE
            return out
    prod_num = K.ONE
    den_const = K.ONE
    for u, tu in enumerate(ts):
        prod_num = prod_num * (z + tu)
        if u != 0:
            den_const = den_const * tu
    factor = prod_num / den_const
    return [factor / (z + ta) for ta in ts]


def bind_low_subspace(table: list[K], weights: list[K]) -> list[K]:
    """Bind the low k variables of table against weights = lagrange_subspace_weights(k, z)."""
    dom = len(weights)
    if dom == 0 or (dom & (dom - 1)) or len(table) % dom != 0:
        raise ValueError("table length must be a multiple of len(weights)")
    out = []
    for b in range(len(table) // dom):
        acc = K.ZERO
        base = b * dom
        for a, w in enumerate(weights):
            acc = acc + w * table[base + a]
        out.append(acc)
    return out


def sumcheck_prove_skip(claim: K, tables: list[list[K]], combine, degree: int,
                        k: int, transcript: Transcript, label: bytes
                        ) -> tuple[UnivariateSkipProof, list[K], list[K]]:
    """Prove a sum-check with a k-variable univariate skip on round 0 (spec 03.9)."""
    if degree < 1:
        raise ValueError("degree must be >= 1")
    size = len(tables[0])
    if size == 0 or size & (size - 1) or any(len(t) != size for t in tables):
        raise ValueError("tables must share a power-of-two length")
    m = size.bit_length() - 1
    if k < 1 or k > m:
        raise ValueError("skip parameter k must satisfy 1 <= k <= m")
    tables = [[x if isinstance(x, K) else K(int(x)) for x in t] for t in tables]
    _init(transcript, label, claim, m, degree)
    dom = 1 << k
    ds = degree * (dom - 1)
    blocks = size // dom
    s_evals = []
    for j in range(ds + 1):
        if j < dom:
            acc = K.ZERO
            for b in range(blocks):
                idx = j + dom * b
                acc = acc + combine([T[idx] for T in tables])
            s_evals.append(acc)
        else:
            w = lagrange_subspace_weights(k, K.t(j))
            bound = [bind_low_subspace(T, w) for T in tables]
            acc = K.ZERO
            for b in range(blocks):
                acc = acc + combine([T[b] for T in bound])
            s_evals.append(acc)
    sub_sum = K.ZERO
    for v in s_evals[:dom]:
        sub_sum = sub_sum + v
    if sub_sum != claim:
        raise ValueError("claim inconsistent with tables on skipped subspace")
    skip_msg = [v for j, v in enumerate(s_evals) if j != dom - 1]
    transcript.absorb_ks(label + b"/skip/msg", skip_msg)
    r0 = transcript.challenge_k(label + b"/skip/chal")
    cur = interpolate_eval(s_evals, r0)
    w_r0 = lagrange_subspace_weights(k, r0)
    tables = [bind_low_subspace(T, w_r0) for T in tables]
    msgs, rs = [], [r0]
    for _ in range(m - k):
        half = len(tables[0]) // 2
        ev = {}
        for j in range(degree + 1):
            t = K.t(j)
            acc = K.ZERO
            for i in range(half):
                vals = [T[2 * i] + t * (T[2 * i] + T[2 * i + 1]) for T in tables]
                acc = acc + combine(vals)
            ev[j] = acc
        if ev[0] + ev[1] != cur:
            raise ValueError("claim inconsistent with tables (g(0)+g(1) != claim)")
        msg = [ev[0]] + [ev[j] for j in range(2, degree + 1)]
        transcript.absorb_ks(label + b"/msg", msg)
        r = transcript.challenge_k(label + b"/chal")
        msgs.append(msg)
        rs.append(r)
        cur = interpolate_eval([ev[j] for j in range(degree + 1)], r)
        tables = [bind_low(T, r) for T in tables]
    return UnivariateSkipProof(skip_msg, msgs), rs, [T[0] for T in tables]


def sumcheck_verify_skip(claim: K, num_vars: int, degree: int, k: int,
                         proof: UnivariateSkipProof, transcript: Transcript,
                         label: bytes) -> tuple[list[K], K]:
    """Verify a univariate-skip sum-check proof (spec 03.9)."""
    if degree < 1:
        raise ValueError("degree must be >= 1")
    if k < 1 or k > num_vars or k > 16:
        raise VerificationError("invalid skip parameter k")
    dom = 1 << k
    ds = degree * (dom - 1)
    rem = num_vars - k
    if len(proof.skip_msg) != ds or not all(isinstance(x, K) for x in proof.skip_msg):
        raise VerificationError("malformed skip round message")
    if len(proof.round_msgs) != rem:
        raise VerificationError("wrong number of rounds")
    _init(transcript, label, claim, num_vars, degree)
    transcript.absorb_ks(label + b"/skip/msg", proof.skip_msg)
    r0 = transcript.challenge_k(label + b"/skip/chal")
    derived = claim
    for v in proof.skip_msg[:dom - 1]:
        derived = derived + v
    s_evals = list(proof.skip_msg[:dom - 1]) + [derived] + list(proof.skip_msg[dom - 1:])
    cur = interpolate_eval(s_evals, r0)
    rs = [r0]
    for msg in proof.round_msgs:
        if len(msg) != degree or not all(isinstance(x, K) for x in msg):
            raise VerificationError("malformed round message")
        transcript.absorb_ks(label + b"/msg", msg)
        r = transcript.challenge_k(label + b"/chal")
        ys = [msg[0], cur + msg[0]] + list(msg[1:])
        cur = interpolate_eval(ys, r)
        rs.append(r)
    return rs, cur
