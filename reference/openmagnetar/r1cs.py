"""Sparse R1CS / SIMD R1CS structures (docs/spec/06-spartan.md sections 6.1-6.2).

A structure has 2^rho rows and 2^nu columns. The vector z = (w, 1, x) has length
2^nu: w occupies indices [0, 2^(nu-1)), index 2^(nu-1) holds the constant 1,
then the public input x, then zeros. Entries live in B (field='B', values 0/1)
or K (field='K').
"""

from __future__ import annotations

from dataclasses import dataclass, field as dc_field

from .field import K
from .mle import eq_table


def _k(x) -> K:
    return x if isinstance(x, K) else K(int(x))


class SparseMatrix:
    """2^rho x 2^nu matrix with a dict of non-zero entries {(row, col): K}."""

    def __init__(self, rho: int, nu: int, entries: dict):
        self.rho, self.nu = rho, nu
        self.entries: dict[tuple[int, int], K] = {}
        for (r, c), v in entries.items():
            if not (0 <= r < 1 << rho and 0 <= c < 1 << nu):
                raise ValueError("matrix entry out of range")
            v = _k(v)
            if v:
                self.entries[(r, c)] = v

    def mul_vec(self, z: list) -> list[K]:
        """M z. z entries are bits (ints 0/1) or K. For bit z the result is an XOR of entries."""
        out = [0] * (1 << self.rho)
        for (r, c), v in self.entries.items():
            zc = z[c]
            if isinstance(zc, int):
                if zc:
                    out[r] ^= v.v
            else:
                out[r] ^= (v * zc).v
        return [K(o) for o in out]

    def mle(self, r_row: list[K], r_col: list[K]) -> K:
        """M~(r_row, r_col) = sum_{(r,c)} M[r][c] eq(r_row, r) eq(r_col, c), in O(nnz) after the eq tables."""
        if len(r_row) != self.rho or len(r_col) != self.nu:
            raise ValueError("point length mismatch")
        er, ec = eq_table(r_row), eq_table(r_col)
        acc = K.ZERO
        for (r, c), v in self.entries.items():
            acc = acc + v * er[r] * ec[c]
        return acc

    def fold_rows(self, r_row: list[K]) -> list[K]:
        """Table over columns: c -> sum_r eq(r_row, r) M[r][c]  (= M~(r_row, c))."""
        if len(r_row) != self.rho:
            raise ValueError("point length mismatch")
        er = eq_table(r_row)
        out = [K.ZERO] * (1 << self.nu)
        for (r, c), v in self.entries.items():
            out[c] = out[c] + v * er[r]
        return out


@dataclass
class R1CS:
    """Base structure s = (A, B, C). `field` is 'B' or 'K'."""
    field: str
    rho: int
    nu: int
    A: SparseMatrix
    B: SparseMatrix
    C: SparseMatrix

    def __post_init__(self):
        if self.field not in ("B", "K"):
            raise ValueError("field must be 'B' or 'K'")
        for M in (self.A, self.B, self.C):
            if (M.rho, M.nu) != (self.rho, self.nu):
                raise ValueError("matrix dimension mismatch")
            if self.field == "B" and any(v.v > 1 for v in M.entries.values()):
                raise ValueError("B-relation entries must be 0/1")

    @property
    def mats(self):
        return (self.A, self.B, self.C)

    def check_instance(self, z: list) -> bool:
        a, b, c = (M.mul_vec(z) for M in self.mats)
        return all(x * y == w for x, y, w in zip(a, b, c))


def build_z(w: list[int], x: list, nu: int) -> list[int | K]:
    """z = (w, 1, x), zero padded to 2^nu. len(w) must be 2^(nu-1); 1 + len(x) <= 2^(nu-1)."""
    half = 1 << (nu - 1)
    if len(w) != half:
        raise ValueError("witness must have exactly 2^(nu-1) entries (pad with zeros)")
    if 1 + len(x) > half:
        raise ValueError("public input too long")
    z = list(w) + [1] + list(x)
    return z + [0] * ((1 << nu) - len(z))


def public_part(x: list, nu: int) -> list:
    """(1, x) zero padded to 2^(nu-1)."""
    half = 1 << (nu - 1)
    if 1 + len(x) > half:
        raise ValueError("public input too long")
    p = [K.ONE] + [_k(v) for v in x]
    return p + [K.ZERO] * (half - len(p))


def check_witness_bits(W: list[list[int]], nu: int) -> None:
    for row in W:
        if len(row) != 1 << (nu - 1) or any(b not in (0, 1) for b in row):
            raise ValueError("W must be a bit matrix with 2^(nu-1) columns")


def simd_satisfied(structs: list[R1CS], W: list[list[int]], X: list[list]) -> bool:
    """All relations hold on every row (the shared-witness SIMD relation of paper 5.1)."""
    if len(W) != len(X):
        raise ValueError("W and X must have one row per instance")
    nu = structs[0].nu
    check_witness_bits(W, nu)
    return all(s.check_instance(build_z(w, x, nu)) for s in structs for w, x in zip(W, X))


def flatten_W(W: list[list[int]]) -> list[int]:
    """Row-major flattening, index = column + (2^(nu-1)) * instance (CONVENTIONS C2 exception)."""
    return [b for row in W for b in row]
