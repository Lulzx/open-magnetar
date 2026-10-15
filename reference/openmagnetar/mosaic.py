"""MosaicPCS layout, lifting and batching sum-check (docs/spec/05-mosaic.md)."""

from __future__ import annotations

from dataclasses import dataclass

from .field import K
from .mle import eq_eval, eq_table, mle_eval
from .sumcheck import SumcheckProof, VerificationError, sumcheck_prove, sumcheck_verify
from .transcript import Transcript

LABEL = b"mos"


@dataclass(frozen=True)
class Claim:
    """Evaluation claim p~_{comp_id}(point) = value on a component polynomial."""
    comp_id: int
    point: tuple
    value: K

    def __post_init__(self):
        object.__setattr__(self, "point", tuple(self.point))


@dataclass(frozen=True)
class Placement:
    comp_id: int
    log_size: int
    offset: int   # first index of the subcube in G
    suffix: int   # offset >> log_size


@dataclass
class Layout:
    ell: int
    placements: list[Placement]   # in canonical (layout) order

    def by_id(self) -> dict[int, Placement]:
        return {p.comp_id: p for p in self.placements}

    def suffix_bits(self, p: Placement) -> list[int]:
        return [(p.suffix >> k) & 1 for k in range(self.ell - p.log_size)]


def compute_layout(components: list[tuple[int, int]], ell_min: int = 0) -> Layout:
    """components: (id, log_size). Sort by (log_size desc, id asc), pack sequentially.
    Because sizes are non-increasing powers of two, every offset is a multiple of the size."""
    if not components:
        raise ValueError("empty component list")
    ids = [c[0] for c in components]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate component id")
    for cid, ls in components:
        if not (0 <= cid < 1 << 32) or ls < 0:
            raise ValueError("bad component")
    order = sorted(components, key=lambda c: (-c[1], c[0]))
    placements, cur = [], 0
    for cid, ls in order:
        assert cur % (1 << ls) == 0
        placements.append(Placement(cid, ls, cur, cur >> ls))
        cur += 1 << ls
    total_log = (cur - 1).bit_length() if cur > 1 else 0
    ell = max(total_log, ell_min, max((ls for _, ls in components), default=0))
    return Layout(ell, placements)


def build_G(layout: Layout, tables: dict[int, list[int]]) -> list[int]:
    G = [0] * (1 << layout.ell)
    for p in layout.placements:
        t = tables[p.comp_id]
        if len(t) != 1 << p.log_size or any(b not in (0, 1) for b in t):
            raise ValueError("component must be a bit table of 2^log_size entries")
        G[p.offset:p.offset + len(t)] = t
    return G


def lift_point(layout: Layout, claim: Claim) -> list[K]:
    """Eq. (4): r || s_i (suffix in the high variables)."""
    p = layout.by_id().get(claim.comp_id)
    if p is None:
        raise VerificationError("claim on unknown component")
    if len(claim.point) != p.log_size:
        raise VerificationError("claim point has wrong length")
    return list(claim.point) + [K(b) for b in layout.suffix_bits(p)]


@dataclass
class BatchProof:
    sumcheck: SumcheckProof
    v_G: K


def _alpha_powers(alpha: K, n: int) -> list[K]:
    out, p = [], K.ONE
    for _ in range(n):
        out.append(p)
        p = p * alpha
    return out


def _start(claims: list[Claim], transcript: Transcript):
    transcript.absorb_ks(LABEL + b"/batch/claims", [c.value for c in claims])
    return transcript.challenge_k(LABEL + b"/batch/gamma")


def eq_sum_table(layout: Layout, claims: list[Claim], alphas: list[K]) -> list[K]:
    """Sum_i alpha_i eq(r_i || s_i, x) for all x. The suffix factor is an indicator, so
    claim i only touches its own subcube."""
    T = [K.ZERO] * (1 << layout.ell)
    pl = layout.by_id()
    for a, c in zip(alphas, claims):
        p = pl[c.comp_id]
        et = eq_table(list(c.point))
        for x, e in enumerate(et):
            T[p.offset + x] = T[p.offset + x] + a * e
    return T


MAX_CLAIMS = 256   # 05.4: powers-of-gamma batching loses (n-1)/|K|; <= 256 keeps 120 bits


def batch_prove(layout: Layout, claims: list[Claim], G: list[int], transcript: Transcript):
    """Returns (BatchProof, r_G, v_G). Claims must be true for G."""
    if len(claims) > MAX_CLAIMS:
        raise ValueError("too many Mosaic claims for powers-of-gamma batching (05.4)")
    for c in claims:
        lift_point(layout, c)
    alpha = _start(claims, transcript)
    alphas = _alpha_powers(alpha, len(claims))
    claim = K.ZERO
    for a, c in zip(alphas, claims):
        claim = claim + a * c.value
    E = eq_sum_table(layout, claims, alphas)
    proof, r_G, fin = sumcheck_prove(claim, [E, [K(b) for b in G]], lambda v: v[0] * v[1], 2,
                                     transcript, LABEL + b"/batch")
    v_G = fin[1]
    transcript.absorb_k(LABEL + b"/vg", v_G)
    return BatchProof(proof, v_G), r_G, v_G


def batch_verify(layout: Layout, claims: list[Claim], proof: BatchProof, transcript: Transcript):
    """Returns (r_G, v_G): the claim G~(r_G) = v_G handed to ring switching."""
    if len(claims) > MAX_CLAIMS:
        raise VerificationError("too many Mosaic claims for powers-of-gamma batching (05.4)")
    lifted = [lift_point(layout, c) for c in claims]
    alpha = _start(claims, transcript)
    alphas = _alpha_powers(alpha, len(claims))
    claim = K.ZERO
    for a, c in zip(alphas, claims):
        claim = claim + a * c.value
    r_G, e = sumcheck_verify(claim, layout.ell, 2, proof.sumcheck, transcript, LABEL + b"/batch")
    transcript.absorb_k(LABEL + b"/vg", proof.v_G)
    ew = K.ZERO
    for a, pt in zip(alphas, lifted):
        ew = ew + a * eq_eval(pt, r_G)
    if ew * proof.v_G != e:
        raise VerificationError("mosaic batching: final check failed")
    return r_G, proof.v_G


def direct_G_eval(G: list[int], point: list[K]) -> K:
    return mle_eval(G, point)
