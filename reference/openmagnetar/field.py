"""Binary fields per docs/spec/CONVENTIONS.md C1.

K = GF(2^128) = GF(2)[X]/(X^128 + X^7 + X^2 + X + 1). An element is the 128-bit
integer whose bit i is the coefficient of X^i. This module favours clarity over speed.
"""

from __future__ import annotations

MODULUS = (1 << 128) | 0x87
MASK = (1 << 128) - 1


def clmul(a: int, b: int) -> int:
    """Carry-less product of two non-negative integers (4-bit windows)."""
    if a.bit_length() < b.bit_length():
        a, b = b, a
    if b < 2:
        return a if b else 0
    t1 = a
    t2 = a << 1
    t3 = t2 ^ a
    t4 = a << 2
    t5 = t4 ^ a
    t6 = t4 ^ t2
    t7 = t6 ^ a
    tbl = (0, t1, t2, t3, t4, t5, t6, t7)
    r = 0
    shift = ((b.bit_length() + 2) // 3 - 1) * 3
    while shift >= 0:
        r = (r << 3) ^ tbl[(b >> shift) & 7]
        shift -= 3
    return r


def reduce(r: int) -> int:
    """Reduce a polynomial (as int) modulo MODULUS (fold the high part twice)."""
    while r >> 128:
        h = r >> 128
        r = (r & MASK) ^ h ^ (h << 1) ^ (h << 2) ^ (h << 7)
    return r


class K:
    __slots__ = ("v",)

    def __init__(self, v: int = 0):
        if not 0 <= v <= MASK:
            raise ValueError("K element out of range")
        self.v = v

    # construction / encoding
    @staticmethod
    def t(k: int) -> "K":
        """The field point t_k (integer value k), CONVENTIONS C1."""
        return K(k)

    @staticmethod
    def from_bytes(b: bytes) -> "K":
        if len(b) != 16:
            raise ValueError("K encoding is 16 bytes")
        return K(int.from_bytes(b, "little"))

    def to_bytes(self) -> bytes:
        return self.v.to_bytes(16, "little")

    def hex(self) -> str:
        return self.to_bytes().hex()

    @staticmethod
    def from_hex(s: str) -> "K":
        return K.from_bytes(bytes.fromhex(s))

    @staticmethod
    def pack(bits) -> "K":
        """Pack up to 128 bits with basis beta_j = X^j (CONVENTIONS C1)."""
        v = 0
        for j, bit in enumerate(bits):
            if bit not in (0, 1):
                raise ValueError("pack expects bits")
            v |= bit << j
        if v > MASK:
            raise ValueError("more than 128 bits")
        return K(v)

    def unpack(self) -> list[int]:
        return [(self.v >> j) & 1 for j in range(128)]

    # arithmetic
    @staticmethod
    def _coerce(o) -> "K":
        if isinstance(o, K):
            return o
        if o in (0, 1):  # embedding of B
            return K(o)
        raise TypeError(f"cannot coerce {o!r} to K")

    def __add__(self, o):
        return K(self.v ^ K._coerce(o).v)

    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__

    def __neg__(self):
        return self

    def __mul__(self, o):
        return K(reduce(clmul(self.v, K._coerce(o).v)))

    __rmul__ = __mul__

    def __pow__(self, e: int):
        if e < 0:
            return self.inv() ** (-e)
        r, b = K(1), self
        while e:
            if e & 1:
                r = r * b
            b = b * b
            e >>= 1
        return r

    def square(self) -> "K":
        """Frobenius map x -> x^2."""
        return self * self

    def inv(self) -> "K":
        if self.v == 0:
            raise ZeroDivisionError("inverse of zero in K")
        return self ** ((1 << 128) - 2)

    def __truediv__(self, o):
        return self * K._coerce(o).inv()

    def is_zero(self) -> bool:
        return self.v == 0

    def __bool__(self):
        return self.v != 0

    def __eq__(self, o):
        if isinstance(o, K):
            return self.v == o.v
        if isinstance(o, int) and o in (0, 1):
            return self.v == o
        return NotImplemented

    def __hash__(self):
        return hash(("K", self.v))

    def __repr__(self):
        return f"K(0x{self.v:032x})"


K.ZERO = K(0)
K.ONE = K(1)
K.X = K(2)


def random_k(rng) -> K:
    """Uniform K element from a random.Random-like rng (tests only)."""
    return K(rng.getrandbits(128))
