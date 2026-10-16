"""Ligerito over K (Novakovic-Angeris structure, all arithmetic in K=GF(2^128)).
Normative description: docs/spec/04-pcs.md section 4.4 and 4.6.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field

from . import ntt
from .field import K
from .hashing import Hasher
from .merkle import MerkleTree, verify_multi
from .mle import eq_table, mle_eval
from .sumcheck import (SumcheckProof, VerificationError, sumcheck_prove,
                       sumcheck_verify)
from .transcript import Transcript


# ----------------------------------------------------------------- parameters
@dataclass(frozen=True)
class LigeritoParams:
    n: int                    # variables of the committed (packed) polynomial
    ks: tuple[int, ...]       # fold arity per committed level (rows = 2^k_i)
    rs: tuple[int, ...]       # log2(1/rate) per committed level
    ts: tuple[int, ...]       # number of queries per committed level
    gs: tuple[int, ...] = ()  # gap-amplification repetitions per level (13.5); () means all 1

    def __post_init__(self):
        if not (len(self.ks) == len(self.rs) == len(self.ts) >= 1):
            raise ValueError("ks, rs, ts must have equal non-zero length")
        if any(k < 1 for k in self.ks) or any(r < 1 for r in self.rs) or any(t < 1 for t in self.ts):
            raise ValueError("k, r, t must be >= 1")
        if self.gs and (len(self.gs) != len(self.ks) or any(g < 1 for g in self.gs)):
            raise ValueError("gs must match ks and be >= 1")
        if sum(self.ks) >= self.n:
            raise ValueError("folds must leave at least one variable (final polynomial)")

    def reps(self, i: int) -> int:
        return self.gs[i] if self.gs else 1

    def sbits(self, i: int) -> int:
        """Extra variables of the level-(i+1) polynomial: ceil(log2 gs_i) (spec 4.4a)."""
        return (self.reps(i) - 1).bit_length()

    @property
    def levels(self) -> int:
        return len(self.ks)

    def n_i(self, i: int) -> int:  # variables of the level-i polynomial (n_0 = n; i = L: final)
        return self.n - sum(self.ks[:i]) + sum(self.sbits(j) for j in range(i))

    def m_i(self, i: int) -> int:  # variables of one folded row g^(j) of level i
        return self.n_i(i) - self.ks[i]

    @property
    def n_final(self) -> int:
        return self.n_i(self.levels)

    def log_codeword(self, i: int) -> int:  # log2 N_i
        return self.m_i(i) + self.rs[i]

    def encode(self) -> bytes:
        u = lambda x: x.to_bytes(8, "little")
        out = u(self.n) + u(self.levels)
        for k, r, t in zip(self.ks, self.rs, self.ts):
            out += u(k) + u(r) + u(t)
        if any(self.reps(i) > 1 for i in range(self.levels)):  # versioned extension (13.5)
            out += b"GAPREPS" + b"".join(u(self.reps(i)) for i in range(self.levels))
        return out


def queries_provable(r: int, bits: int) -> int:
    """t = ceil(bits / -log2((1+rho)/2)), rho = 2^-r (unique-decoding radius)."""
    rho = 2.0 ** -r
    return math.ceil(bits / -math.log2((1 + rho) / 2))


def queries_conjectured(r: int, bits: int) -> int:
    return math.ceil(bits / r)


def schedule(n: int, final: int = 6, max_k: int = 5) -> list[int]:
    """Fold arities: split n - final over ceil((n-final)/max_k) levels, larger first."""
    total = n - final
    if total < 1:
        raise ValueError("n too small")
    L = -(-total // max_k)
    base, extra = divmod(total, L)
    return [base + 1 if i < extra else base for i in range(L)]


def gap_bits_single(k: int, log_n_cw: int) -> float:
    """Bits of the conservative proximity-gap term k*N/|K| for one fold challenge."""
    return 128 - math.log2(k * (1 << log_n_cw))


def gap_reps(k: int, log_n_cw: int, bits: int = 120) -> int:
    """Smallest m with (kN/|K|)^m <= 2^-bits (13.5, gap amplification)."""
    return max(1, math.ceil(bits / gap_bits_single(k, log_n_cw)))


def make_params(n: int, profile: str = "provable-120", r: int = 2) -> LigeritoParams:
    ks = schedule(n)
    if profile == "provable-120":
        if not (2 <= r <= 8):
            raise ValueError("provable-120 requires 2 <= r <= 8")
        t = queries_provable(r, 120)
        base = LigeritoParams(n, tuple(ks), (r,) * len(ks), (t,) * len(ks))
        gs = tuple(gap_reps(k, base.log_codeword(i)) for i, k in enumerate(ks))
        p = LigeritoParams(n, tuple(ks), (r,) * len(ks), (t,) * len(ks),
                           gs if any(g > 1 for g in gs) else ())
        for sb in soundness_bits(p, "provable-120"):
            if min(sb["sumcheck"], sb["batch"], sb["gap"], sb["query"]) < 120.0:
                raise ValueError(f"provable-120 soundness bound violated: {sb}")
        return p
    elif profile == "conjectured-100":
        if not (1 <= r <= 8):
            raise ValueError("conjectured-100 requires 1 <= r <= 8")
        t = queries_conjectured(r, 100)
    else:
        raise ValueError("unknown profile")
    return LigeritoParams(n, tuple(ks), (r,) * len(ks), (t,) * len(ks))


def soundness_bits(p: LigeritoParams, profile: str = "provable-120") -> list[dict]:
    """Per-level error terms (log2 of 1/error) under the formulas of spec 4.7."""
    out = []
    for i in range(p.levels):
        rho = 2.0 ** -p.rs[i]
        delta = (1 - rho) / 2
        N = 1 << p.log_codeword(i)
        k, t = p.ks[i], p.ts[i]
        d = dict(level=i, sumcheck=127 - math.log2(k), batch=128 - math.log2(t),
                 gap=p.reps(i) * (128 - math.log2(k * N)))
        d["query"] = t * -math.log2(1 - delta) if profile == "provable-120" else t * p.rs[i]
        out.append(d)
    return out


# ------------------------------------------------------------------ structures
@dataclass
class LevelData:
    f: list[K]
    k: int
    r: int
    cw: list[list[K]]           # cw[row][q]
    tree: MerkleTree

    def column(self, q: int) -> list[K]:
        return [row[q] for row in self.cw]


@dataclass
class LevelOpening:
    columns: list[list[K]]      # one column per (sorted, deduplicated) query index
    auth: list[bytes]


@dataclass
class LigeritoProof:
    roots: list[bytes]                  # roots of committed levels 1..L-1
    sumchecks: list[SumcheckProof]      # one per level, k_i rounds
    openings: list[LevelOpening]        # one per level
    final: list[K]                      # f_L, 2^n_final elements, in the clear

    def to_bytes(self) -> bytes:
        out = b"".join(self.roots)
        for sc in self.sumchecks:
            for m in sc.round_msgs:
                out += b"".join(x.to_bytes() for x in m)
        for op in self.openings:
            for col in op.columns:
                out += b"".join(x.to_bytes() for x in col)
            out += b"".join(op.auth)
        return out + b"".join(x.to_bytes() for x in self.final)


def column_bytes(col: list[K]) -> bytes:
    return b"".join(x.to_bytes() for x in col)


def commit_level(h: Hasher, f: list[K], k: int, r: int) -> LevelData:
    R = 1 << k
    C = len(f) // R
    cw = [ntt.encode([f[i + R * j] for j in range(C)], r) for i in range(R)]
    N = len(cw[0])
    tree = MerkleTree(h, [column_bytes([cw[i][q] for i in range(R)]) for q in range(N)])
    return LevelData(f, k, r, cw, tree)


def commit(p: LigeritoParams, h: Hasher, table: list[K]) -> tuple[bytes, LevelData]:
    if len(table) != 1 << p.n:
        raise ValueError("table must have 2^n entries")
    ld = commit_level(h, [x if isinstance(x, K) else K(int(x)) for x in table], p.ks[0], p.rs[0])
    return ld.tree.root, ld


def absorb_setup(p: LigeritoParams, root: bytes, tr: Transcript) -> None:
    tr.absorb_bytes(b"pcs/params", p.encode())
    tr.absorb_bytes(b"pcs/root", root)


# product-form weight terms: alpha * prod_b (c_b + d_b x_b)
Term = tuple  # (alpha: K, cs: list[K], ds: list[K])


def term_table(term: Term) -> list[K]:
    alpha, cs, ds = term
    t = [alpha]
    for c, d in zip(cs, ds):
        t = [e * c for e in t] + [e * (c + d) for e in t]
    return t  # index LSB-first: entry j = alpha*prod_b (c_b + d_b j_b)


def sample_indices(tr: Transcript, bits: int, t: int) -> list[int]:
    return sorted({tr.challenge_index(b"pcs/query/idx", bits) for _ in range(t)})


def fold_table(f: list[K], k: int, rho: list[K]) -> list[K]:
    """g[y] = sum_a eq(rho, a) f[a + 2^k y]  (bind the low k variables)."""
    R = 1 << k
    er = eq_table(rho)
    return [sum((e * x for e, x in zip(er, f[y * R:(y + 1) * R])), K.ZERO) for y in range(len(f) // R)]


def selector(j: int, s: int) -> tuple[list[K], list[K]]:
    """Product-form terms (c, d) of eq(bits(j), z) over the s extra variables."""
    return [K.ONE + K((j >> u) & 1) for u in range(s)], [K.ONE] * s


def open_(p: LigeritoParams, h: Hasher, ld0: LevelData, r: list[K], y: K,
          tr: Transcript) -> LigeritoProof:
    """Prover. The transcript must already contain setup (absorb_setup)."""
    if len(r) != p.n:
        raise ValueError("point has wrong length")
    tr.absorb_ks(b"pcs/point", r)
    tr.absorb_k(b"pcs/value", y)
    f, b, c = ld0.f, eq_table(r), y
    ld = ld0
    roots, scs, ops = [], [], []
    for i in range(p.levels):
        k, reps, s, m = p.ks[i], p.reps(i), p.sbits(i), p.m_i(i)
        R, C = 1 << k, len(f) >> k
        tabs = [f[y_ * R:(y_ + 1) * R] for y_ in range(C)] + [b[y_ * R:(y_ + 1) * R] for y_ in range(C)]
        proof, rho, fin = sumcheck_prove(c, tabs, lambda v, C=C: sum((v[a] * v[C + a] for a in range(C)), K.ZERO),
                                         2, tr, b"pcs/sumcheck")
        scs.append(proof)
        g, bp = fin[:C], fin[C:]
        cp = sum((x * z for x, z in zip(g, bp)), K.ZERO)
        rhos = [rho] + [tr.challenge_ks(b"pcs/fold", k) for _ in range(reps - 1)]
        F = list(g)
        for rj in rhos[1:]:
            F += fold_table(f, k, rj)
        F += [K.ZERO] * ((1 << (m + s)) - len(F))
        last = i == p.levels - 1
        if last:
            tr.absorb_ks(b"pcs/final", F)
            nxt = None
        else:
            nxt = commit_level(h, F, p.ks[i + 1], p.rs[i + 1])
            roots.append(nxt.tree.root)
            tr.absorb_bytes(b"pcs/root", nxt.tree.root)
        idx = sample_indices(tr, p.log_codeword(i), p.ts[i])
        cols = [ld.column(q) for q in idx]
        ops.append(LevelOpening(cols, ld.tree.open(idx)))
        tr.absorb_ks(b"pcs/cols", [x for col in cols for x in col])
        if last:
            final = F
            break
        betas = [tr.challenge_k(b"pcs/beta") for _ in range(reps)]
        ers = [eq_table(rj) for rj in rhos]
        c = cp
        b = list(bp) + [K.ZERO] * ((1 << (m + s)) - len(bp))
        off = 1 << m
        for j in range(reps):
            pw = K.ONE
            for q, col in zip(idx, cols):
                pw = pw * betas[j]
                vq = sum((e * x for e, x in zip(ers[j], col)), K.ZERO)
                c = c + pw * vq
                row = ntt.basis_row(q, m, p.log_codeword(i))
                for u in range(off):
                    b[j * off + u] = b[j * off + u] + pw * row[u]
        f, ld = F, nxt
    return LigeritoProof(roots, scs, ops, final)


def verify(p: LigeritoParams, h: Hasher, root: bytes, r: list[K], y: K,
           proof: LigeritoProof, tr: Transcript) -> None:
    """Verifier. Raises VerificationError. Transcript must contain setup."""
    if len(r) != p.n:
        raise VerificationError("point has wrong length")
    if (len(proof.roots) != p.levels - 1 or len(proof.sumchecks) != p.levels
            or len(proof.openings) != p.levels or len(proof.final) != 1 << p.n_final):
        raise VerificationError("malformed proof")
    tr.absorb_ks(b"pcs/point", r)
    tr.absorb_k(b"pcs/value", y)
    terms: list[Term] = [(K.ONE, [K.ONE + x for x in r], [K.ONE] * p.n)]
    c = y
    cur_root = root
    for i in range(p.levels):
        k, reps, s, m = p.ks[i], p.reps(i), p.sbits(i), p.m_i(i)
        rho, cp = sumcheck_verify(c, k, 2, proof.sumchecks[i], tr, b"pcs/sumcheck")
        # fold the first k variables; the sum-check claim concerns block z = 0 of the next polynomial
        zc, zd = selector(0, s)
        terms = [(a * _prod(cs[:k], ds[:k], rho), cs[k:] + zc, ds[k:] + zd) for a, cs, ds in terms]
        rhos = [rho] + [tr.challenge_ks(b"pcs/fold", k) for _ in range(reps - 1)]
        last = i == p.levels - 1
        if last:
            tr.absorb_ks(b"pcs/final", proof.final)
        else:
            tr.absorb_bytes(b"pcs/root", proof.roots[i])
        lb = p.log_codeword(i)
        idx = sample_indices(tr, lb, p.ts[i])
        op = proof.openings[i]
        if len(op.columns) != len(idx) or any(len(col) != 1 << k for col in op.columns):
            raise VerificationError("malformed opening")
        verify_multi(h, cur_root, 1 << lb, idx, [column_bytes(col) for col in op.columns], op.auth)
        tr.absorb_ks(b"pcs/cols", [x for col in op.columns for x in col])
        ers = [eq_table(rj) for rj in rhos]
        vs = [[sum((e * x for e, x in zip(er, col)), K.ZERO) for col in op.columns] for er in ers]
        if last:
            F = proof.final
            for j in range(reps):
                g = F[j << m:(j + 1) << m]
                for q, vq in zip(idx, vs[j]):
                    row = ntt.basis_row(q, m, lb)
                    if sum((a * z for a, z in zip(g, row)), K.ZERO) != vq:
                        raise VerificationError("final polynomial inconsistent with opened column")
            tabs = [term_table(t) for t in terms]
            tot = K.ZERO
            for j in range(len(F)):
                bj = K.ZERO
                for tb in tabs:
                    bj = bj + tb[j]
                tot = tot + F[j] * bj
            if tot != cp:
                raise VerificationError("final inner-product claim fails")
            return
        betas = [tr.challenge_k(b"pcs/beta") for _ in range(reps)]
        c = cp
        for j in range(reps):
            pw = K.ONE
            jc, jd = selector(j, s)
            for q, vq in zip(idx, vs[j]):
                pw = pw * betas[j]
                c = c + pw * vq
                a = ntt.gen_weights(q, m, lb)
                terms.append((pw, [K.ONE] * m + jc, [K.ONE + x for x in a] + jd))
        cur_root = proof.roots[i]


def _prod(cs, ds, rho) -> K:
    acc = K.ONE
    for c, d, x in zip(cs, ds, rho):
        acc = acc * (c + d * x)
    return acc
