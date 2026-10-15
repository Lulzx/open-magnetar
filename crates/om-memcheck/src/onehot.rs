//! Address decomposition, the Frobenius one-hot check (`Δ⋆`) and address
//! virtualization (spec 07 §7.1–7.3). Mirrors
//! `reference/openmagnetar/onehot.py` byte for byte in its transcript
//! interaction.
//!
//! Conventions (CONVENTIONS C2): a component table `A_i` has index
//! `u + 2^ac * j` (address chunk `u` in the LOW bits, cycle `j` in the
//! high bits). Component 1 holds the lowest `ac` bits of the address.
//! Points are lists of `K`, `x_1` first. Bit tables are `bool` vectors
//! (Python `list[int]` of 0/1).

use om_field::K;
use om_sumcheck::{
    SumcheckProof, VerificationError, combine_sum, eq_eval, eq_table, sumcheck_prove,
    sumcheck_verify,
};
use om_transcript::Transcript;
use rayon::prelude::*;

use crate::sublabel;

/// Tables at least this large use rayon (exact elementwise maps / XOR sums).
pub(crate) const PAR_THRESHOLD: usize = 1 << 14;

/// An evaluation claim on a committed polynomial: `poly~(point) = value`
/// (Python `onehot.EvalClaim`; spec 07 §7.1's `(poly, point, value)`).
///
/// The protocol layer turns these into `om_mosaic::Claim`s by resolving
/// `poly` through its component-id map (Python `protocol._to_mosaic`);
/// see [`EvalClaim::to_mosaic_claim`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalClaim {
    pub poly: String,
    pub point: Vec<K>,
    pub value: K,
}

impl EvalClaim {
    /// The `om_mosaic::Claim` for this claim under component id `comp_id`
    /// (Python `protocol._to_mosaic`).
    pub fn to_mosaic_claim(&self, comp_id: i64) -> om_mosaic::Claim {
        om_mosaic::Claim {
            comp_id,
            point: self.point.clone(),
            value: self.value,
        }
    }
}

/// The Boolean point for integer `x`: entry `i` is bit `i` of `x`
/// (LSB first), embedded in `K`.
pub fn bits_of(x: u64, n: usize) -> Vec<K> {
    (0..n).map(|i| K::from_bit((x >> i) & 1 == 1)).collect()
}

// ---------------------------------------------------------------- addresses

/// Chunks of an address; chunk 0 (component 1) is the lowest `a/d` bits.
///
/// # Panics
/// Panics if `d` does not divide `a` (via the shift arithmetic Python
/// would silently truncate; callers in this crate assert first).
pub fn split_addr(addr: usize, a: usize, d: usize) -> Vec<usize> {
    let ac = a / d;
    (0..d)
        .map(|i| (addr >> (i * ac)) & ((1usize << ac) - 1))
        .collect()
}

/// `d` flat 0/1 tables, each of length `2^ac * T`, index `u + 2^ac * j`.
///
/// # Panics
/// Panics unless `d | a` and `a >= d` (Python `assert`).
pub fn comp_tables(addrs: &[usize], a: usize, d: usize) -> Vec<Vec<bool>> {
    assert!(
        a.is_multiple_of(d) && a >= d,
        "comp_tables: need d | a and a >= d"
    );
    let (ac, t) = (a / d, addrs.len());
    let nu = 1usize << ac;
    let mut out = vec![vec![false; nu * t]; d];
    for (j, &ad) in addrs.iter().enumerate() {
        for (i, ch) in split_addr(ad, a, d).into_iter().enumerate() {
            out[i][ch + nu * j] = true;
        }
    }
    out
}

/// The virtual full-address table `ra(k, j) = prod_i A_i(k^(i), j)`,
/// flat index `k + 2^a * j`. Works for arbitrary (also non-one-hot)
/// bit tables.
pub fn full_table(comps: &[Vec<bool>], a: usize, d: usize, t: usize) -> Vec<bool> {
    let (ac, nk) = (a / d, 1usize << a);
    let nu = 1usize << ac;
    let mask = nu - 1;
    // Flat index `k + nk * j`; each entry is an AND of `d` component bits,
    // independent per entry.
    let entry = |idx: usize| {
        let (k, j) = (idx % nk, idx / nk);
        (0..d).all(|i| comps[i][((k >> (i * ac)) & mask) + nu * j])
    };
    if nk * t >= PAR_THRESHOLD {
        (0..nk * t).into_par_iter().map(entry).collect()
    } else {
        (0..nk * t).map(entry).collect()
    }
}

/// Split an address point `r_k ∈ K^a` into its `d` chunk points of
/// length `ac = a/d` (chunk 1 = low variables).
pub fn split_point(r_k: &[K], a: usize, d: usize) -> Vec<Vec<K>> {
    let ac = a / d;
    (0..d).map(|i| r_k[i * ac..(i + 1) * ac].to_vec()).collect()
}

/// `g(j) = sum_u eq(r, u) * table[u + 2^ac j]` (MLE in the `u`
/// variables only), for `j = 0..t`.
pub fn partial_eval_rows(table: &[bool], ac: usize, t: usize, r: &[K]) -> Vec<K> {
    let e = eq_table(r);
    let nu = 1usize << ac;
    let row = |j: usize| {
        let mut acc = K::ZERO;
        for u in 0..nu {
            if table[u + nu * j] {
                acc += e[u];
            }
        }
        acc
    };
    if table.len() >= PAR_THRESHOLD {
        (0..t).into_par_iter().map(row).collect()
    } else {
        (0..t).map(row).collect()
    }
}

// ------------------------------------------------------------ one-hot check

/// Returns `(r', C)` with `c_h = 1 + r_h + r_h^2`, `r'_h = r_h^3 / c_h`,
/// `C = Π_h c_h`, or `None` if some `c_h` is zero (spec 07 §7.2).
pub fn onehot_aux(r: &[K]) -> Option<(Vec<K>, K)> {
    let mut rp = Vec::with_capacity(r.len());
    let mut c_prod = K::ONE;
    for &rh in r {
        let c = K::ONE + rh + rh * rh;
        if c.is_zero() {
            return None;
        }
        rp.push(rh * rh * rh / c);
        c_prod *= c;
    }
    Some((rp, c_prod))
}

/// Draw `r ∈ K^ac` (all coordinates in one call, label `label ‖ "/r"`),
/// retrying the whole draw while some `c_h = 0` (spec 07 §7.2
/// resampling rule). Returns `(r, r', C)`.
pub fn sample_onehot_point(
    transcript: &mut Transcript,
    label: &[u8],
    ac: usize,
) -> (Vec<K>, Vec<K>, K) {
    let r_label = sublabel(label, b"/r");
    loop {
        let r = transcript.challenge_ks(&r_label, ac);
        if let Some((rp, c)) = onehot_aux(&r) {
            return (r, rp, c);
        }
    }
}

/// Proof of the one-hot check (spec 07 §7.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OneHotProof {
    pub sc: SumcheckProof,
    /// Per component: `[Ã(r ∥ s), Ã(r' ∥ s)]`.
    pub evals: Vec<Vec<K>>,
}

fn onehot_combine(lam: &[K], c: K, v: &[K]) -> K {
    let mut acc = K::ZERO;
    for (x, &l) in lam.iter().enumerate() {
        let (xv, yv) = (v[1 + 2 * x], v[2 + 2 * x]);
        acc += l * (xv * xv * xv + c * yv);
    }
    v[0] * acc
}

/// Prove that every row of every component has Hamming weight at most
/// one (spec 07 §7.2, degree-4 sum-check over the `n` cycle variables).
/// Returns the proof and, per component in order, the claims
/// `(name, r ∥ s, e)`, `(name, r' ∥ s, e')`.
pub fn onehot_prove(
    comps: &[Vec<bool>],
    names: &[String],
    ac: usize,
    n: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (OneHotProof, Vec<EvalClaim>) {
    let t = 1usize << n;
    let (r, rp, c) = sample_onehot_point(transcript, label, ac);
    let rho = transcript.challenge_ks(&sublabel(label, b"/rho"), n);
    let lam = transcript.challenge_ks(&sublabel(label, b"/lambda"), comps.len());
    let mut tables = vec![eq_table(&rho)];
    for a in comps {
        tables.push(partial_eval_rows(a, ac, t, &r));
        tables.push(partial_eval_rows(a, ac, t, &rp));
    }
    let lam_c = lam.clone();
    let combine = move |v: &[K]| onehot_combine(&lam_c, c, v);
    // The honest prover sums its actual tables (0 for valid rows).
    let claim = combine_sum(&tables, &combine);
    let (sc, s, mles) = sumcheck_prove(
        claim,
        tables,
        &combine,
        4,
        transcript,
        &sublabel(label, b"/sc"),
    );
    let evals: Vec<Vec<K>> = (0..comps.len())
        .map(|x| vec![mles[1 + 2 * x], mles[2 + 2 * x]])
        .collect();
    let flat: Vec<K> = evals.iter().flatten().copied().collect();
    transcript.absorb_ks(&sublabel(label, b"/evals"), &flat);
    let claims = onehot_claims(names, &r, &rp, &s, &evals);
    (OneHotProof { sc, evals }, claims)
}

fn onehot_claims(names: &[String], r: &[K], rp: &[K], s: &[K], evals: &[Vec<K>]) -> Vec<EvalClaim> {
    let mut claims = Vec::with_capacity(2 * names.len());
    for (x, nm) in names.iter().enumerate() {
        let mut p1 = r.to_vec();
        p1.extend_from_slice(s);
        claims.push(EvalClaim {
            poly: nm.clone(),
            point: p1,
            value: evals[x][0],
        });
        let mut p2 = rp.to_vec();
        p2.extend_from_slice(s);
        claims.push(EvalClaim {
            poly: nm.clone(),
            point: p2,
            value: evals[x][1],
        });
    }
    claims
}

/// Verify the one-hot check (spec 07 §7.2), returning the output claims
/// in the same order as [`onehot_prove`].
///
/// # Errors
/// Returns [`VerificationError`] on malformed evals, a failing
/// sum-check, or a failing final check.
pub fn onehot_verify(
    names: &[String],
    ac: usize,
    n: usize,
    proof: &OneHotProof,
    transcript: &mut Transcript,
    label: &[u8],
) -> Result<Vec<EvalClaim>, VerificationError> {
    let (r, rp, c) = sample_onehot_point(transcript, label, ac);
    let rho = transcript.challenge_ks(&sublabel(label, b"/rho"), n);
    let lam = transcript.challenge_ks(&sublabel(label, b"/lambda"), names.len());
    let (s, expected) = sumcheck_verify(
        K::ZERO,
        n,
        4,
        &proof.sc,
        transcript,
        &sublabel(label, b"/sc"),
    )?;
    if proof.evals.len() != names.len() || proof.evals.iter().any(|e| e.len() != 2) {
        return Err(VerificationError::new("onehot: malformed evals"));
    }
    let flat: Vec<K> = proof.evals.iter().flatten().copied().collect();
    transcript.absorb_ks(&sublabel(label, b"/evals"), &flat);
    let mut acc = K::ZERO;
    for (x, &l) in lam.iter().enumerate() {
        let (xv, yv) = (proof.evals[x][0], proof.evals[x][1]);
        acc += l * (xv * xv * xv + c * yv);
    }
    if eq_eval(&rho, &s) * acc != expected {
        return Err(VerificationError::new("onehot: final check failed"));
    }
    Ok(onehot_claims(names, &r, &rp, &s, &proof.evals))
}

// ------------------------------------------------------ address virtualization

/// One virtualization term: the already-absorbed claim
/// `ra~(r_k ‖ cyc) = value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirtTerm {
    /// Cycle point `c ∈ K^n`.
    pub cyc: Vec<K>,
    /// Claimed `ra~(r_k ‖ c)`.
    pub value: K,
}

/// One virtualization group: `d` component names, an address point, and
/// its terms (spec 07 §7.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirtGroup {
    /// `d` polynomial names, component 1 first.
    pub names: Vec<String>,
    /// `K^a`, the address point.
    pub r_k: Vec<K>,
    pub terms: Vec<VirtTerm>,
}

/// Proof of address virtualization (`d > 1` only; `d = 1` proves
/// nothing).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirtProof {
    pub sc: SumcheckProof,
    /// Per group, per component (flattened group-major).
    pub evals: Vec<K>,
}

fn virt_direct(groups: &[VirtGroup]) -> Vec<EvalClaim> {
    let mut out = Vec::new();
    for g in groups {
        for t in &g.terms {
            let mut point = g.r_k.clone();
            point.extend_from_slice(&t.cyc);
            out.push(EvalClaim {
                poly: g.names[0].clone(),
                point,
                value: t.value,
            });
        }
    }
    out
}

fn virt_claims(groups: &[VirtGroup], d: usize, s: &[K], evals: &[K], a: usize) -> Vec<EvalClaim> {
    let mut out = Vec::with_capacity(groups.len() * d);
    for (gi, g) in groups.iter().enumerate() {
        for (i, rc) in split_point(&g.r_k, a, d).into_iter().enumerate() {
            let mut point = rc;
            point.extend_from_slice(s);
            out.push(EvalClaim {
                poly: g.names[i].clone(),
                point,
                value: evals[gi * d + i],
            });
        }
    }
    out
}

/// Reduce the claims `ra~(r_k ‖ c_t) = v_t` to component claims
/// (spec 07 §7.3). For `d = 1` nothing is proven and the proof is
/// `None`: each term already is a component claim. `comps_per_group[g]`
/// holds the `d` component tables of group `g`.
pub fn virt_prove(
    groups: &[VirtGroup],
    comps_per_group: &[Vec<Vec<bool>>],
    a: usize,
    d: usize,
    n: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (Option<VirtProof>, Vec<EvalClaim>) {
    if d == 1 {
        return (None, virt_direct(groups));
    }
    let (t, ac) = (1usize << n, a / d);
    let nterms: usize = groups.iter().map(|g| g.terms.len()).sum();
    let nu = transcript.challenge_ks(&sublabel(label, b"/nu"), nterms);
    let mut tables: Vec<Vec<K>> = groups
        .iter()
        .flat_map(|g| g.terms.iter().map(|term| eq_table(&term.cyc)))
        .collect();
    let base = tables.len();
    for (gi, g) in groups.iter().enumerate() {
        for (i, rc) in split_point(&g.r_k, a, d).into_iter().enumerate() {
            tables.push(partial_eval_rows(&comps_per_group[gi][i], ac, t, &rc));
        }
    }
    // Table layout: one eq table per term (group-major), then d per group.
    let term_counts: Vec<usize> = groups.iter().map(|g| g.terms.len()).collect();
    let combine = {
        let nu = nu.clone();
        let term_counts = term_counts.clone();
        move |v: &[K]| {
            let (mut acc, mut tpos) = (K::ZERO, 0usize);
            for (gi, &cnt) in term_counts.iter().enumerate() {
                let mut coef = K::ZERO;
                for _ in 0..cnt {
                    coef += nu[tpos] * v[tpos];
                    tpos += 1;
                }
                let mut prod = coef;
                for i in 0..d {
                    prod *= v[nterms + gi * d + i];
                }
                acc += prod;
            }
            acc
        }
    };
    // The honest prover sums the actual tables (not the claimed value).
    let claim = combine_sum(&tables, &combine);
    let (sc, s, mles) = sumcheck_prove(
        claim,
        tables,
        &combine,
        d + 1,
        transcript,
        &sublabel(label, b"/sc"),
    );
    let evals = mles[base..].to_vec();
    transcript.absorb_ks(&sublabel(label, b"/evals"), &evals);
    let claims = virt_claims(groups, d, &s, &evals, a);
    (Some(VirtProof { sc, evals }), claims)
}

/// Verify address virtualization (spec 07 §7.3). For `d = 1` the proof
/// is ignored and each term is returned as a component claim.
///
/// # Errors
/// Returns [`VerificationError`] if the proof is missing (for `d > 1`),
/// malformed, or a check fails.
pub fn virt_verify(
    groups: &[VirtGroup],
    a: usize,
    d: usize,
    n: usize,
    proof: Option<&VirtProof>,
    transcript: &mut Transcript,
    label: &[u8],
) -> Result<Vec<EvalClaim>, VerificationError> {
    if d == 1 {
        return Ok(virt_direct(groups));
    }
    let proof = proof.ok_or_else(|| VerificationError::new("virt: missing proof"))?;
    let nterms: usize = groups.iter().map(|g| g.terms.len()).sum();
    let nu = transcript.challenge_ks(&sublabel(label, b"/nu"), nterms);
    let mut claim = K::ZERO;
    let mut tpos = 0usize;
    for g in groups {
        for t in &g.terms {
            claim += nu[tpos] * t.value;
            tpos += 1;
        }
    }
    let (s, expected) = sumcheck_verify(
        claim,
        n,
        d + 1,
        &proof.sc,
        transcript,
        &sublabel(label, b"/sc"),
    )?;
    if proof.evals.len() != groups.len() * d {
        return Err(VerificationError::new("virt: wrong number of evals"));
    }
    transcript.absorb_ks(&sublabel(label, b"/evals"), &proof.evals);
    let (mut acc, mut tpos) = (K::ZERO, 0usize);
    for (gi, g) in groups.iter().enumerate() {
        let mut coef = K::ZERO;
        for t in &g.terms {
            coef += nu[tpos] * eq_eval(&t.cyc, &s);
            tpos += 1;
        }
        let mut prod = coef;
        for i in 0..d {
            prod *= proof.evals[gi * d + i];
        }
        acc += prod;
    }
    if acc != expected {
        return Err(VerificationError::new("virt: final check failed"));
    }
    Ok(virt_claims(groups, d, &s, &proof.evals, a))
}
