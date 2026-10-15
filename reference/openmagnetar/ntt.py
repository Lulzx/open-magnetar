"""Additive NTT / Reed-Solomon over K, novel polynomial basis (Lin-Chung-Han).
Normative description: docs/spec/04-pcs.md section 4.3.

Domain: U_m = span{beta_0..beta_{m-1}}, beta_b = X^b, i.e. the K elements with
integer value q < 2^m; omega_q = K(q).  Novel basis X_j = prod_{b in bits(j)} What_b,
What_b = W_b / W_b(beta_b), W_b = prod_{u in span(beta_0..beta_{b-1})} (x - u).
"""

from __future__ import annotations

from .field import K

_WH: list[list[K]] = []  # _WH[i][b] = What_i(beta_b), defined for b >= i


def _ensure(m: int) -> None:
    """Make _WH cover i, b < m."""
    if len(_WH) >= m and (not _WH or len(_WH[0]) >= m):
        return
    _WH.clear()
    w = [K(1 << b) for b in range(m)]  # w[b] = W_i(beta_b), i = 0
    for i in range(m):
        s = w[i]
        sinv = s.inv()
        _WH.append([K.ZERO] * i + [w[b] * sinv for b in range(i, m)])
        w = [w[b] * (w[b] + s) if b > i else K.ZERO for b in range(m)]  # W_{i+1}(beta_b)


def what_beta(i: int, b: int) -> K:
    _ensure(max(i, b) + 1)
    return _WH[i][b]


def gen_weights(q: int, mu: int, m: int) -> list[K]:
    """[What_b(omega_q) for b < mu], for q < 2^m."""
    _ensure(m)
    out = []
    for b in range(mu):
        acc = 0
        for c in range(b, m):
            if (q >> c) & 1:
                acc ^= _WH[b][c].v
        out.append(K(acc))
    return out


def basis_row(q: int, mu: int, m: int) -> list[K]:
    """[X_j(omega_q) for j < 2^mu] (the generator-matrix column for position q)."""
    a = gen_weights(q, mu, m)
    t = [K.ONE]
    for ab in a:
        t = t + [e * ab for e in t]
    return t


def encode_naive(msg: list[K], log_rate: int) -> list[K]:
    mu = len(msg).bit_length() - 1
    if len(msg) != 1 << mu:
        raise ValueError("message length must be a power of two")
    m = mu + log_rate
    out = []
    for q in range(1 << m):
        acc = K.ZERO
        for mj, g in zip(msg, basis_row(q, mu, m)):
            acc = acc + mj * g
        out.append(acc)
    return out


def encode(msg: list[K], log_rate: int) -> list[K]:
    """Fast O(m 2^m) encoding: codeword[q] = sum_j msg[j] X_j(omega_q)."""
    mu = len(msg).bit_length() - 1
    if len(msg) != 1 << mu:
        raise ValueError("message length must be a power of two")
    m = mu + log_rate
    _ensure(m)
    a = list(msg) + [K.ZERO] * ((1 << m) - len(msg))
    for i in range(m - 1, -1, -1):
        half = 1 << i
        for c in range(1 << (m - 1 - i)):
            t = 0
            for d in range(m - 1 - i):
                if (c >> d) & 1:
                    t ^= _WH[i][i + 1 + d].v
            tk = K(t)
            base = c << (i + 1)
            for j in range(base, base + half):
                lo = a[j] + tk * a[j + half]
                a[j] = lo
                a[j + half] = a[j + half] + lo
    return a
