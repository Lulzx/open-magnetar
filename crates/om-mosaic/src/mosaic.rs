//! Layout, lifting (Eq. 4) and the batching sum-check (spec 05
//! §5.2–5.4). Mirrors `reference/openmagnetar/mosaic.py` byte for byte
//! in its transcript interaction: base label `mos/batch` (absorbing
//! `mos/batch/claims`, squeezing `mos/batch/gamma`, then the sum-check's
//! own sublabels) and `mos/vg` for the final value `v_G`.

use std::collections::BTreeMap;

use om_field::K;
use om_sumcheck::{
    PackedBits, SumcheckProof, VerificationError, batch_claims, bind_low_in_place, eq_eval,
    eq_table, interpolate_eval, mle_eval_bits, sumcheck_init, sumcheck_verify,
};
use om_transcript::Transcript;
use rayon::prelude::*;

/// Transcript label prefix of this section (Python `mosaic.LABEL`).
pub const LABEL: &[u8] = b"mos";

/// Cap on batched claims (spec 05 §5.4): powers-of-`γ` batching loses
/// `(n-1)/|K|`; `n <= 256` keeps 120 bits.
pub const MAX_CLAIMS: usize = 256;

/// An evaluation claim `p~_{comp_id}(point) = value` on a component
/// polynomial (spec 05 §5.3).
///
/// `comp_id` is `i64` because `om-spartan`'s no-layout mode emits a
/// whole-witness claim with Python's sentinel `comp_id = -1`; genuine
/// component ids are in `[0, 2^32)` (enforced by [`compute_layout`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub comp_id: i64,
    pub point: Vec<K>,
    pub value: K,
}

/// Where one component sits in `G`: the aligned subcube starting at
/// `offset`, with `suffix = offset >> log_size` (spec 05 §5.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Placement {
    pub comp_id: i64,
    pub log_size: usize,
    /// First index of the subcube in `G`.
    pub offset: usize,
    /// `offset >> log_size`.
    pub suffix: usize,
}

/// The layout of all components into one hypercube of dimension `ell`
/// (spec 05 §5.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub ell: usize,
    /// In canonical (layout) order: log size descending, id ascending.
    pub placements: Vec<Placement>,
}

impl Layout {
    /// Placements keyed by component id (Python `Layout.by_id`).
    pub fn by_id(&self) -> BTreeMap<i64, &Placement> {
        self.placements.iter().map(|p| (p.comp_id, p)).collect()
    }

    fn placement(&self, comp_id: i64) -> Option<&Placement> {
        self.placements.iter().find(|p| p.comp_id == comp_id)
    }

    /// The suffix as a little-endian bit vector of length
    /// `ell - log_size` (C2): bit `k` is variable `x_{log_size + k + 1}`.
    pub fn suffix_bits(&self, p: &Placement) -> Vec<bool> {
        (0..self.ell - p.log_size)
            .map(|k| (p.suffix >> k) & 1 == 1)
            .collect()
    }
}

/// Compute the layout of `components` (`(id, log_size)` pairs): sort by
/// (log size descending, id ascending) and pack sequentially. Because
/// sizes are non-increasing powers of two, every offset is a multiple
/// of its component's size (spec 05 §5.2). `ell` is the maximum of
/// `ceil_log2(sum 2^log_size)` (with `ceil_log2(1) = 0`), the largest
/// log size, and `ell_min`.
///
/// # Panics
/// Panics where Python raises `ValueError`: an empty component list, a
/// duplicate id, or an id outside `[0, 2^32)`.
pub fn compute_layout(components: &[(i64, usize)], ell_min: usize) -> Layout {
    assert!(!components.is_empty(), "empty component list");
    let mut ids: Vec<i64> = components.iter().map(|c| c.0).collect();
    ids.sort_unstable();
    assert!(
        ids.windows(2).all(|w| w[0] != w[1]),
        "duplicate component id"
    );
    for &(cid, _) in components {
        assert!((0..1 << 32).contains(&cid), "bad component");
    }
    let mut order: Vec<(i64, usize)> = components.to_vec();
    order.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let mut placements = Vec::with_capacity(order.len());
    let mut cur = 0usize;
    for (cid, ls) in order {
        debug_assert_eq!(cur % (1usize << ls), 0);
        placements.push(Placement {
            comp_id: cid,
            log_size: ls,
            offset: cur,
            suffix: cur >> ls,
        });
        cur += 1usize << ls;
    }
    let total_log = if cur > 1 {
        (usize::BITS - (cur - 1).leading_zeros()) as usize
    } else {
        0
    };
    let max_ls = components.iter().map(|c| c.1).max().unwrap_or(0);
    Layout {
        ell: total_log.max(ell_min).max(max_ls),
        placements,
    }
}

/// Assemble `G`: the bit vector of length `2^ell` holding each
/// component table at its offset and zero elsewhere (spec 05 §5.2).
///
/// # Panics
/// Panics if a component's table is missing (Python `KeyError`) or is
/// not a bit table of `2^log_size` entries (Python `ValueError`; a
/// `bool` table is bit-valued by construction, so only the length can
/// fail).
pub fn build_g(layout: &Layout, tables: &BTreeMap<i64, Vec<bool>>) -> Vec<bool> {
    let mut g = vec![false; 1usize << layout.ell];
    for p in &layout.placements {
        let t = tables
            .get(&p.comp_id)
            .unwrap_or_else(|| panic!("missing table for component {}", p.comp_id));
        assert_eq!(
            t.len(),
            1usize << p.log_size,
            "component must be a bit table of 2^log_size entries"
        );
        g[p.offset..p.offset + t.len()].copy_from_slice(t);
    }
    g
}

/// Lift a claim point to `G`: `r ∥ s_i`, the suffix bits as `K` elements
/// 0/1 in the high variables (Eq. 4, spec 05 §5.3).
///
/// # Errors
/// Returns [`VerificationError`] if the component id is unknown or the
/// point length is not the component's log size.
pub fn lift_point(layout: &Layout, claim: &Claim) -> Result<Vec<K>, VerificationError> {
    let p = layout
        .placement(claim.comp_id)
        .ok_or_else(|| VerificationError::new("claim on unknown component"))?;
    if claim.point.len() != p.log_size {
        return Err(VerificationError::new("claim point has wrong length"));
    }
    let mut out = claim.point.clone();
    out.extend(layout.suffix_bits(p).iter().map(|&b| K::from_bit(b)));
    Ok(out)
}

/// A batching proof: the sum-check proof, then `v_G` (spec 05 §5.4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchProof {
    pub sumcheck: SumcheckProof,
    pub v_g: K,
}

/// [`build_g`] in packed form: component tables are packed bit
/// tables and the assembled `G` is returned packed, so neither is
/// ever expanded to a byte per bit. The bits are identical.
///
/// # Panics
/// As [`build_g`].
pub fn build_g_packed(layout: &Layout, tables: &BTreeMap<i64, PackedBits>) -> PackedBits {
    let mut g = PackedBits::zero(1usize << layout.ell);
    for pl in &layout.placements {
        let table = tables
            .get(&pl.comp_id)
            .unwrap_or_else(|| panic!("missing table for component {}", pl.comp_id));
        assert_eq!(
            table.len(),
            1usize << pl.log_size,
            "component must be a bit table of 2^log_size entries"
        );
        for idx in table.iter_ones() {
            g.set(pl.offset + idx);
        }
    }
    g
}

/// The table `E(x) = Σ_j α_j eq(r_j ∥ s_j, x)` (spec 05 §5.4). The
/// suffix factor is an indicator, so claim `j` only touches its own
/// subcube; several claims on one component accumulate there.
///
/// # Panics
/// Panics if `alphas` and `claims` differ in length (Python's `zip`
/// would silently truncate) or a claim names an unknown component
/// (Python `KeyError`).
pub fn eq_sum_table(layout: &Layout, claims: &[Claim], alphas: &[K]) -> Vec<K> {
    assert_eq!(
        alphas.len(),
        claims.len(),
        "eq_sum_table: alphas/claims length mismatch"
    );
    let mut t = vec![K::ZERO; 1usize << layout.ell];
    let pl = layout.by_id();
    for (a, c) in alphas.iter().zip(claims) {
        let p = pl
            .get(&c.comp_id)
            .unwrap_or_else(|| panic!("eq_sum_table: unknown component {}", c.comp_id));
        for (x, e) in eq_table(&c.point).iter().enumerate() {
            t[p.offset + x] += *a * *e;
        }
    }
    t
}

/// Prove the batching sum-check for `claims` against `g` (spec 05
/// §5.4), returning `(proof, r_G, v_G)`. The claims must be true for
/// `g`; their order is the caller's and is never sorted or
/// deduplicated.
///
/// # Panics
/// Panics where Python raises in the prover: more than [`MAX_CLAIMS`]
/// claims (`ValueError`, before any transcript interaction), a claim
/// on an unknown component or with a wrong-length point
/// (`VerificationError` from [`lift_point`]), or a false claim, which
/// the sum-check prover refuses. Also panics if `g` does not have
/// length `2^ell` (the sum-check's table-length check).
pub fn batch_prove(
    layout: &Layout,
    claims: &[Claim],
    g: &[bool],
    transcript: &mut Transcript,
) -> (BatchProof, Vec<K>, K) {
    assert!(
        claims.len() <= MAX_CLAIMS,
        "too many Mosaic claims for powers-of-gamma batching (05.4)"
    );
    for c in claims {
        lift_point(layout, c).unwrap_or_else(|e| panic!("batch_prove: {}", e.message()));
    }
    assert_eq!(
        g.len(),
        1usize << layout.ell,
        "batch_prove: g must have length 2^ell"
    );
    split_batch_prove(
        layout,
        claims,
        &PackedBits::from_bools(g),
        transcript,
        BIT_ROUNDS,
    )
}

/// [`batch_prove`] over a packed `G`: the same proof, without ever
/// expanding `G` (or the eq table) to field elements per bit.
///
/// # Panics
/// As [`batch_prove`], plus if the packed length is not `2^ell`.
pub fn batch_prove_packed(
    layout: &Layout,
    claims: &[Claim],
    g: &PackedBits,
    transcript: &mut Transcript,
) -> (BatchProof, Vec<K>, K) {
    batch_prove_packed_with(layout, claims, g, transcript, BIT_ROUNDS)
}

/// Rounds of the batching sum-check computed straight from the bits
/// of `G`, before the bound tables (`2^(ell - BIT_ROUNDS)` entries
/// each) are materialised for the remaining dense rounds.
pub const BIT_ROUNDS: usize = 10;

/// [`batch_prove_packed`] with an explicit number of bit-level rounds
/// (any value gives the same proof; exposed for tests).
///
/// # Panics
/// As [`batch_prove_packed`].
#[doc(hidden)]
pub fn batch_prove_packed_with(
    layout: &Layout,
    claims: &[Claim],
    g: &PackedBits,
    transcript: &mut Transcript,
    bit_rounds: usize,
) -> (BatchProof, Vec<K>, K) {
    assert!(
        claims.len() <= MAX_CLAIMS,
        "too many Mosaic claims for powers-of-gamma batching (05.4)"
    );
    for c in claims {
        lift_point(layout, c).unwrap_or_else(|e| panic!("batch_prove: {}", e.message()));
    }
    assert_eq!(
        g.len(),
        1usize << layout.ell,
        "batch_prove: g must have length 2^ell"
    );
    split_batch_prove(layout, claims, g, transcript, bit_rounds)
}

/// One claim as the batching prover sees it: its placement, its point
/// lifted to `ell` coordinates, and `alpha_j` times the `eq` factors
/// of the rounds bound so far.
struct BatchTerm<'a> {
    offset: usize,
    log_size: usize,
    point: &'a [K],
    lifted: Vec<K>,
    coef: K,
}

/// Call `f(i)` for each set bit `i` of `words` in `[start, start + len)`,
/// in increasing order, with `i` relative to `start`.
fn for_each_one(words: &[u64], start: usize, len: usize, mut f: impl FnMut(usize)) {
    let end = start + len;
    let mut wi = start / 64;
    while wi * 64 < end {
        let mut w = words[wi];
        let lo = wi * 64;
        if lo < start {
            w &= !0u64 << (start - lo);
        }
        if lo + 64 > end {
            w &= (1u64 << (end - lo)) - 1;
        }
        while w != 0 {
            let b = w.trailing_zeros() as usize;
            w &= w - 1;
            f(lo + b - start);
        }
        wi += 1;
    }
}

/// Elementwise `a += b`.
fn add_into(a: &mut [K], b: &[K]) {
    for (x, y) in a.iter_mut().zip(b) {
        *x += *y;
    }
}

/// Per-position sums for round `r` of the bit-level phase, for the
/// claims `group` that share one region of `G`: for each claim, the
/// vector over positions `p < 2^(r+1)` of
/// `sum_y eq(point[r+1..], y) G(base + p + 2^(r+1) y)`. The `eq`
/// factor is split into two square-root tables so the inner sum over
/// set bits is additions only.
fn region_sums(
    words: &[u64],
    base: usize,
    r: usize,
    nfree: usize,
    group: &[&BatchTerm<'_>],
) -> Vec<Vec<K>> {
    let np = 1usize << (r + 1);
    let h = nfree / 2;
    // With no free coordinates the point may be shorter than `r + 1`.
    let coords = |t: &BatchTerm<'_>, a: usize, b: usize| {
        if a == b {
            Vec::new()
        } else {
            t.point[r + 1 + a..r + 1 + b].to_vec()
        }
    };
    let lo: Vec<Vec<K>> = group.iter().map(|t| eq_table(&coords(t, 0, h))).collect();
    let hi: Vec<Vec<K>> = group
        .iter()
        .map(|t| eq_table(&coords(t, h, nfree)))
        .collect();
    let block = 1usize << (r + 1 + h);
    let zero = || vec![vec![K::ZERO; np]; group.len()];
    let one_block = |mut tot: Vec<Vec<K>>, yhi: usize| {
        let mut acc = zero();
        for_each_one(words, base + yhi * block, block, |l| {
            let (p, ylo) = (l & (np - 1), l >> (r + 1));
            for (a, e) in acc.iter_mut().zip(&lo) {
                a[p] += e[ylo];
            }
        });
        for ((t, a), e) in tot.iter_mut().zip(&acc).zip(&hi) {
            for (x, y) in t.iter_mut().zip(a) {
                if !y.is_zero() {
                    *x += e[yhi] * *y;
                }
            }
        }
        tot
    };
    let nblocks = 1usize << (nfree - h);
    let merge = |mut a: Vec<Vec<K>>, b: Vec<Vec<K>>| {
        for (x, y) in a.iter_mut().zip(&b) {
            add_into(x, y);
        }
        a
    };
    if nblocks * block >= PAR_BITS {
        (0..nblocks)
            .into_par_iter()
            .fold(zero, one_block)
            .reduce(zero, merge)
    } else {
        (0..nblocks).fold(zero(), one_block)
    }
}

/// Regions at least this many bits long are scanned in parallel.
const PAR_BITS: usize = 1 << 16;

/// The batching sum-check over packed `G`. Rounds `0..m` (`m =
/// min(bit_rounds, ell)`) are computed from the bits of `G` directly:
/// the round polynomial is `sum_j coef_j eq(P_jr, t) ((1+t) S_j(0) +
/// t S_j(1))` with `S_j(v) = sum_y eq(P_j[r+1..], y) G(chal, v, y)`,
/// and `G(chal, v, y)` expands over the `2^r` bound positions with an
/// `eq` table of the challenges. After `m` rounds the bound `G` and
/// `E` tables (`2^(ell - m)` entries) are built and the remaining
/// rounds run densely, binding in place. Transcript and proof bytes
/// match the dense definition of spec 05 §5.4.
fn split_batch_prove(
    layout: &Layout,
    claims: &[Claim],
    g: &PackedBits,
    transcript: &mut Transcript,
    bit_rounds: usize,
) -> (BatchProof, Vec<K>, K) {
    let ell = layout.ell;
    let words = g.words();
    let values: Vec<K> = claims.iter().map(|c| c.value).collect();
    let (alphas, claim) = batch_claims(&values, transcript, b"mos/batch");
    let by_id = layout.by_id();
    let mut terms: Vec<BatchTerm<'_>> = claims
        .iter()
        .zip(&alphas)
        .map(|(c, &a)| {
            let p = by_id[&c.comp_id];
            BatchTerm {
                offset: p.offset,
                log_size: p.log_size,
                point: &c.point,
                lifted: lift_point(layout, c).expect("claims pre-checked by caller"),
                coef: a,
            }
        })
        .collect();
    // eq factor of one coordinate: the multilinear `1 + p + v` (C2).
    let eqfac = |p: K, v: K| K::ONE + p + v;
    let label = b"mos/batch".as_slice();
    sumcheck_init(transcript, label, claim, ell, 2);
    let msg_label: Vec<u8> = [label, b"/msg"].concat();
    let chal_label: Vec<u8> = [label, b"/chal"].concat();
    let (mut msgs, mut rs): (Vec<Vec<K>>, Vec<K>) = (Vec::new(), Vec::new());
    let mut cur = claim;
    let tv = [K::t(0), K::t(1), K::t(2)];
    let mut round = |ev: [K; 3], cur: &mut K, rs: &mut Vec<K>, tr: &mut Transcript| -> K {
        assert_eq!(
            ev[0] + ev[1],
            *cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let msg = vec![ev[0], ev[2]];
        tr.absorb_ks(&msg_label, &msg);
        let chal = tr.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(chal);
        *cur = interpolate_eval(&ev, chal);
        chal
    };

    // Phase 1: rounds computed from the bits of G.
    let m = bit_rounds.min(ell);
    for r in 0..m {
        // Claims sharing a region (same component, or small components
        // inside one block of 2^(r+1) bits) share one scan of its bits.
        let mut groups: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
        for (j, t) in terms.iter().enumerate() {
            let nfree = t.log_size.saturating_sub(r + 1);
            let base = t.offset & !((1usize << (r + 1)) - 1);
            groups.entry((base, nfree)).or_default().push(j);
        }
        let eqc = eq_table(&rs[..r]);
        let half = 1usize << r;
        let mut ev = [K::ZERO; 3];
        for ((base, nfree), js) in &groups {
            let group: Vec<&BatchTerm<'_>> = js.iter().map(|&j| &terms[j]).collect();
            let sums = region_sums(words, *base, r, *nfree, &group);
            for (t, tot) in group.iter().zip(&sums) {
                let s0 = (0..half).fold(K::ZERO, |a, b| a + eqc[b] * tot[b]);
                let s1 = (0..half).fold(K::ZERO, |a, b| a + eqc[b] * tot[half + b]);
                let pr = t.lifted[r];
                for (slot, &x) in ev.iter_mut().zip(&tv) {
                    *slot += t.coef * eqfac(pr, x) * ((K::ONE + x) * s0 + x * s1);
                }
            }
        }
        let chal = round(ev, &mut cur, &mut rs, transcript);
        for t in &mut terms {
            t.coef *= eqfac(t.lifted[r], chal);
        }
    }

    // Bound tables: G(chal, z) by byte lookups over each block of 2^m
    // bits, E(chal, z) from the claims' remaining coordinates.
    let n_rest = 1usize << (ell - m);
    let mut gt = bind_bits(words, &eq_table(&rs[..m]), m, n_rest);
    let mut et = vec![K::ZERO; n_rest];
    for t in &terms {
        let z0 = t.offset >> m;
        if t.log_size > m {
            for (i, e) in eq_table(&t.point[m..]).iter().enumerate() {
                et[z0 + i] += t.coef * *e;
            }
        } else {
            et[z0] += t.coef;
        }
    }
    drop(terms);

    // Phase 2: dense rounds on the bound tables.
    for _ in m..ell {
        let half = gt.len() / 2;
        let pair = |i: usize| {
            let (e0, e1, g0, g1) = (et[2 * i], et[2 * i + 1], gt[2 * i], gt[2 * i + 1]);
            let mut ev = [K::ZERO; 3];
            for (slot, &x) in ev.iter_mut().zip(&tv) {
                *slot = (e0 + x * (e0 + e1)) * (g0 + x * (g0 + g1));
            }
            ev
        };
        let sum3 = |a: [K; 3], b: [K; 3]| [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
        let ev = if half >= PAR_BITS {
            (0..half)
                .into_par_iter()
                .map(pair)
                .reduce(|| [K::ZERO; 3], sum3)
        } else {
            (0..half).map(pair).fold([K::ZERO; 3], sum3)
        };
        let chal = round(ev, &mut cur, &mut rs, transcript);
        bind_low_in_place(&mut et, chal);
        bind_low_in_place(&mut gt, chal);
    }
    let v_g = gt[0];
    transcript.absorb_k(b"mos/vg", v_g);
    (
        BatchProof {
            sumcheck: SumcheckProof { round_msgs: msgs },
            v_g,
        },
        rs,
        v_g,
    )
}

/// `out[z] = sum_b eqm[b] G(z 2^m + b)` for `z < n_out`: the bit table
/// bound in its low `m` variables. Blocks of at least a byte use one
/// 256-entry subset-sum table per byte position.
fn bind_bits(words: &[u64], eqm: &[K], m: usize, n_out: usize) -> Vec<K> {
    let bit = |i: usize| (words[i / 64] >> (i % 64)) & 1 == 1;
    if m < 3 {
        return (0..n_out)
            .map(|z| {
                (0..1usize << m).fold(
                    K::ZERO,
                    |a, b| {
                        if bit((z << m) + b) { a + eqm[b] } else { a }
                    },
                )
            })
            .collect();
    }
    let nbytes = 1usize << (m - 3);
    let tables: Vec<[K; 256]> = (0..nbytes)
        .map(|q| {
            let mut t = [K::ZERO; 256];
            for p in 1..256usize {
                let low = p.trailing_zeros() as usize;
                t[p] = t[p & (p - 1)] + eqm[8 * q + low];
            }
            t
        })
        .collect();
    let byte_at = |i: usize| ((words[i / 8] >> (8 * (i % 8))) & 0xff) as usize;
    let one = |z: usize| (0..nbytes).fold(K::ZERO, |a, q| a + tables[q][byte_at(z * nbytes + q)]);
    if n_out << m >= PAR_BITS {
        (0..n_out).into_par_iter().map(one).collect()
    } else {
        (0..n_out).map(one).collect()
    }
}

/// Verify the batching sum-check (spec 05 §5.4), returning
/// `(r_G, v_G)`: the single claim `G̃(r_G) = v_G` handed to ring
/// switching (§5.5).
///
/// # Errors
/// Returns [`VerificationError`] if there are more than [`MAX_CLAIMS`]
/// claims (checked before any transcript interaction), a claim fails
/// [`lift_point`], the sum-check fails, or the final identity
/// `e = (Σ_j α_j eq(R_j, r_G)) · v_G` does not hold.
pub fn batch_verify(
    layout: &Layout,
    claims: &[Claim],
    proof: &BatchProof,
    transcript: &mut Transcript,
) -> Result<(Vec<K>, K), VerificationError> {
    if claims.len() > MAX_CLAIMS {
        return Err(VerificationError::new(
            "too many Mosaic claims for powers-of-gamma batching (05.4)",
        ));
    }
    let lifted: Vec<Vec<K>> = claims
        .iter()
        .map(|c| lift_point(layout, c))
        .collect::<Result<_, _>>()?;
    let values: Vec<K> = claims.iter().map(|c| c.value).collect();
    let (alphas, claim) = batch_claims(&values, transcript, b"mos/batch");
    let (r_g, e) = sumcheck_verify(
        claim,
        layout.ell,
        2,
        &proof.sumcheck,
        transcript,
        b"mos/batch",
    )?;
    transcript.absorb_k(b"mos/vg", proof.v_g);
    let mut ew = K::ZERO;
    for (a, pt) in alphas.iter().zip(&lifted) {
        ew += *a * eq_eval(pt, &r_g);
    }
    if ew * proof.v_g != e {
        return Err(VerificationError::new(
            "mosaic batching: final check failed",
        ));
    }
    Ok((r_g, proof.v_g))
}

/// Evaluate `G̃` directly (Python `direct_G_eval`): `mle_eval` of a bit
/// table.
pub fn direct_g_eval(g: &[bool], point: &[K]) -> K {
    mle_eval_bits(g, point)
}
