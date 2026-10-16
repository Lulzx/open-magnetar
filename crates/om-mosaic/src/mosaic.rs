//! Layout, lifting (Eq. 4) and the batching sum-check (spec 05
//! §5.2–5.4). Mirrors `reference/openmagnetar/mosaic.py` byte for byte
//! in its transcript interaction: base label `mos/batch` (absorbing
//! `mos/batch/claims`, squeezing `mos/batch/gamma`, then the sum-check's
//! own sublabels) and `mos/vg` for the final value `v_G`.

use std::collections::BTreeMap;

use om_field::K;
use om_sumcheck::{
    PackedBits, SumcheckProof, VerificationError, batch_claims, eq_eval, eq_table,
    interpolate_eval, mle_eval_bits, sumcheck_init, sumcheck_verify,
};
use om_transcript::Transcript;

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
    let set_bits: Vec<usize> = g
        .iter()
        .enumerate()
        .filter_map(|(i, &b)| b.then_some(i))
        .collect();
    sparse_batch_prove(layout, claims, &set_bits, transcript)
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
    let set_bits: Vec<usize> = g.iter_ones().collect();
    sparse_batch_prove(layout, claims, &set_bits, transcript)
}

/// The batching sum-check over the set bits of `G`, shared by
/// [`batch_prove`] and [`batch_prove_packed`]. Entries are keyed by
/// the remaining suffix after the rounds so far and carry the bound
/// `(E, G)` values at that suffix; suffixes with bound `G = 0` are
/// dropped and their `E` is recomputed on demand from the lifted
/// claim points when a sibling needs it. No table of `2^ell` field
/// elements is materialised; transcript and proof bytes match the
/// dense definition.
fn sparse_batch_prove(
    layout: &Layout,
    claims: &[Claim],
    set_bits: &[usize],
    transcript: &mut Transcript,
) -> (BatchProof, Vec<K>, K) {
    let ell = layout.ell;
    let lifted: Vec<Vec<K>> = claims
        .iter()
        .map(|c| lift_point(layout, c).expect("claims pre-checked by caller"))
        .collect();
    let values: Vec<K> = claims.iter().map(|c| c.value).collect();
    let (alphas, claim) = batch_claims(&values, transcript, b"mos/batch");
    // eq factor of bit position `b` for point coordinate `p` and
    // variable value `v`: multilinear extension `1 + p + v` (C2).
    let eqfac = |p: K, v: K| K::ONE + p + v;
    // E at the remaining suffix `key` in round `r`, given the bound
    // prefix products `prefix[j] = prod_{b<r} eqfac(p_{j,b}, chal_b)`.
    let e_at = |key: usize, r: usize, prefix: &[K]| -> K {
        let mut acc = K::ZERO;
        for (j, pt) in lifted.iter().enumerate() {
            let mut prod = alphas[j] * prefix[j];
            for (i, &pb) in pt.iter().enumerate().skip(r) {
                prod *= eqfac(pb, K::from_bit((key >> (i - r)) & 1 == 1));
                if prod.is_zero() {
                    break;
                }
            }
            acc += prod;
        }
        acc
    };
    let mut prefix = vec![K::ONE; claims.len()];
    // Suffix -> bound G value; only suffixes with bound G != 0 are
    // stored. E is never stored: `e_at` recomputes it exactly.
    let mut entries: BTreeMap<usize, K> = set_bits.iter().map(|&x| (x, K::ONE)).collect();
    let label = b"mos/batch".as_slice();
    sumcheck_init(transcript, label, claim, ell, 2);
    let msg_label: Vec<u8> = [label, b"/msg"].concat();
    let chal_label: Vec<u8> = [label, b"/chal"].concat();
    let (mut msgs, mut rs): (Vec<Vec<K>>, Vec<K>) = (Vec::new(), Vec::new());
    let mut cur = claim;
    for r in 0..ell {
        let mut ev = [K::ZERO; 3];
        let mut iter = entries.iter().peekable();
        while let Some((&k, &gv)) = iter.next() {
            let parent = k / 2;
            let (mut gp, mut ep) = ([gv, K::ZERO], [K::ZERO, K::ZERO]);
            if k % 2 == 0 {
                ep[0] = e_at(k, r, &prefix);
                ep[1] = e_at(k + 1, r, &prefix);
                if let Some(&(&k2, &g2)) = iter.peek()
                    && k2 == k + 1
                {
                    gp[1] = g2;
                    iter.next();
                }
            } else {
                gp[1] = gp[0];
                gp[0] = K::ZERO;
                ep[0] = e_at(k - 1, r, &prefix);
                ep[1] = e_at(k, r, &prefix);
            }
            let _ = parent;
            for (kk, slot) in ev.iter_mut().enumerate() {
                let tv = K::t(kk as u128);
                let e_t = ep[0] + tv * (ep[0] + ep[1]);
                let g_t = gp[0] + tv * (gp[0] + gp[1]);
                *slot += e_t * g_t;
            }
        }
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let msg = vec![ev[0], ev[2]];
        transcript.absorb_ks(&msg_label, &msg);
        let chal = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(chal);
        cur = interpolate_eval(&ev, chal);
        for (j, pt) in lifted.iter().enumerate() {
            prefix[j] *= eqfac(pt[r], chal);
        }
        let mut next: BTreeMap<usize, K> = BTreeMap::new();
        let mut iter = entries.into_iter().peekable();
        while let Some((k, g0)) = iter.next() {
            let (ga, gb) = if k % 2 == 0 {
                match iter.peek() {
                    Some((k2, _)) if *k2 == k + 1 => {
                        let (_, g1) = iter.next().expect("peeked entry");
                        (g0, g1)
                    }
                    _ => (g0, K::ZERO),
                }
            } else {
                (K::ZERO, g0)
            };
            let g_new = ga + chal * (ga + gb);
            if !g_new.is_zero() {
                next.insert(k / 2, g_new);
            }
        }
        entries = next;
    }
    let v_g = entries.get(&0).copied().unwrap_or(K::ZERO);
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
