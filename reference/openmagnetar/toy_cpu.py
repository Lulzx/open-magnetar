"""Toy two-relation example for the Virtual Spartan reference tests and vectors.

Per SIMD instance: a 4-bit accumulator step acc_out = acc_in + a (mod 16), as a ripple-carry
adder over B, plus a packed mux y = sel * x over K (x, y are 4-bit groups packed with X^i).
Cross-step: IN[j] = OUT[j-1]; IN[0] = init = 0; OUT[q-1] = fin (public).
nu = 6 (64 columns of z, 32 witness columns), rho = 3 (8 rows).
"""

from __future__ import annotations

from .field import K
from .r1cs import R1CS, SparseMatrix
from .spartan import CrossStep, Segment

RHO, NU = 3, 6
ONE = 1 << (NU - 1)
IN, OUT, A, CARRY, XC, YC, SEL = 0, 4, 8, 12, 16, 20, 24

SEG_IN, SEG_OUT, SEG_A, SEG_CARRY, SEG_X, SEG_Y, SEG_SEL, SEG_PAD = 1, 2, 3, 4, 5, 6, 7, 8


def structs() -> list[R1CS]:
    a, b, c = {}, {}, {}
    b[(0, ONE)] = 1
    a[(0, CARRY)] = 1
    for i in range(4):
        r = 1 + i
        for col in (IN + i, A + i, CARRY + i, OUT + i):
            a[(r, col)] = 1
        b[(r, ONE)] = 1
    for i in range(3):
        r = 5 + i
        a[(r, IN + i)] = a[(r, CARRY + i)] = 1
        b[(r, A + i)] = b[(r, CARRY + i)] = 1
        c[(r, CARRY + i + 1)] = c[(r, CARRY + i)] = 1
    bin_ = R1CS("B", RHO, NU, SparseMatrix(RHO, NU, a), SparseMatrix(RHO, NU, b), SparseMatrix(RHO, NU, c))
    fa = {(0, SEL): K(1), (1, SEL): K.t(1 << 5)}
    fb, fc = {}, {}
    for i in range(4):
        for r in (0, 1):
            fb[(r, XC + i)] = K(1 << i)
        fc[(0, YC + i)] = K(1 << i)
        fc[(1, YC + i)] = K(1 << (5 + i))
    fld = R1CS("K", RHO, NU, SparseMatrix(RHO, NU, fa), SparseMatrix(RHO, NU, fb), SparseMatrix(RHO, NU, fc))
    return [bin_, fld]


def segments() -> list[Segment]:
    return [
        Segment(SEG_IN, "virtual", 2, IN >> 2), Segment(SEG_OUT, "virtual", 2, OUT >> 2),
        Segment(SEG_A, "direct", 2, A >> 2), Segment(SEG_CARRY, "direct", 2, CARRY >> 2),
        Segment(SEG_X, "direct", 2, XC >> 2), Segment(SEG_Y, "direct", 2, YC >> 2),
        Segment(SEG_SEL, "direct", 0, SEL), Segment(SEG_PAD, "pad", 2, 7),
    ]


def witness(rng, q: int, init: int = 0):
    """Returns (W, X, cross) with honest data."""
    W, acc = [], init
    for _ in range(q):
        row = [0] * (1 << (NU - 1))
        a = rng.getrandbits(4)
        c = 0
        for i in range(4):
            ib, ab = (acc >> i) & 1, (a >> i) & 1
            row[IN + i], row[A + i], row[CARRY + i] = ib, ab, c
            row[OUT + i] = ib ^ ab ^ c
            c = (ib & ab) | (ib & c) | (ab & c)
        sel, x = rng.getrandbits(1), rng.getrandbits(4)
        row[SEL] = sel
        for i in range(4):
            row[XC + i] = (x >> i) & 1
            row[YC + i] = sel & ((x >> i) & 1)
        acc = (acc + a) & 15
        W.append(row)
    X = [[] for _ in range(q)]
    cross = CrossStep(SEG_IN, SEG_OUT, [(init >> i) & 1 for i in range(4)], [(acc >> i) & 1 for i in range(4)])
    return W, X, cross
