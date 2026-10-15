"""Multilinear extensions and eq (docs/spec/03-sumcheck.md), C2 ordering."""

from __future__ import annotations

from .field import K


def eq_eval(x: list[K], y: list[K]) -> K:
    if len(x) != len(y):
        raise ValueError("length mismatch")
    acc = K.ONE
    for a, b in zip(x, y):
        acc = acc * (K.ONE + a + b)
    return acc


def eq_table(r: list[K]) -> list[K]:
    """Entry i = eq(r, bits(i)), bit j of i (LSB first) paired with r[j]."""
    t = [K.ONE]
    for rj in r:
        lo = [e * (K.ONE + rj) for e in t]  # b_j = 0
        hi = [e * rj for e in t]            # b_j = 1
        t = lo + hi
    return t


def _as_k(x) -> K:
    return x if isinstance(x, K) else K(1 if x else 0) if x in (0, 1) else K._coerce(x)


def bind_low(table: list[K], r: K) -> list[K]:
    """Fix x_1 = r: out[i] = T[2i] + r (T[2i] + T[2i+1])."""
    if len(table) % 2:
        raise ValueError("table length must be even")
    return [_as_k(table[2 * i]) + r * (_as_k(table[2 * i]) + _as_k(table[2 * i + 1]))
            for i in range(len(table) // 2)]


def mle_eval(table: list, r: list[K]) -> K:
    if len(table) != 1 << len(r):
        raise ValueError("table length must be 2^len(r)")
    t = [_as_k(e) for e in table]
    for ri in r:
        t = bind_low(t, ri)
    return t[0]
