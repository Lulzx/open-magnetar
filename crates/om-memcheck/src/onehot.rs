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
    PackedBits, SumcheckProof, VerificationError, eq_eval, eq_table, sumcheck_verify,
};
use om_transcript::Transcript;
use rayon::prelude::*;

use crate::lazy::{SplitEq, sumcheck_prove_rows};
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

/// The `d` address component tables of one access stream (spec 07
/// §7.10: "one-hot components are stored as the index
/// `chunk_i(addr[j])` per cycle").
///
/// The honest prover holds [`AddrComps::Addrs`]: one address per cycle,
/// so the tables are `O(T)` integers instead of `d · 2^ac · T` bits.
/// [`AddrComps::Bits`] holds arbitrary bit tables (rows of Hamming
/// weight other than one), used by tests of cheating provers; every
/// prover accepts both and produces the same bytes for equal tables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AddrComps {
    /// Component `i` of cycle `j` is one-hot at `chunk_i(addrs[j])`.
    Addrs {
        addrs: Vec<u32>,
        /// Address bits.
        a: usize,
        /// Components, `d | a`.
        d: usize,
    },
    /// `d` flat bit tables, index `u + 2^ac * j` (as [`comp_tables`]).
    Bits { tables: Vec<Vec<bool>>, ac: usize },
}

impl AddrComps {
    /// Components of the given per-cycle addresses.
    ///
    /// # Panics
    /// Panics unless `d | a`, `a >= d`, `a <= 32` and every address is
    /// below `2^a`.
    pub fn from_addrs(addrs: Vec<u32>, a: usize, d: usize) -> Self {
        assert!(
            a.is_multiple_of(d) && a >= d && a <= 32,
            "AddrComps: need d | a, a >= d and a <= 32"
        );
        assert!(
            addrs.iter().all(|&x| (u64::from(x)) < 1u64 << a),
            "AddrComps: address out of range"
        );
        AddrComps::Addrs { addrs, a, d }
    }

    /// [`AddrComps::from_addrs`] from `usize` addresses.
    pub fn from_usizes(addrs: &[usize], a: usize, d: usize) -> Self {
        let v = addrs
            .iter()
            .map(|&x| u32::try_from(x).expect("address fits in u32"))
            .collect();
        Self::from_addrs(v, a, d)
    }

    /// Number of components `d`.
    pub fn d(&self) -> usize {
        match self {
            AddrComps::Addrs { d, .. } => *d,
            AddrComps::Bits { tables, .. } => tables.len(),
        }
    }

    /// Bits per component `ac = a/d`.
    pub fn ac(&self) -> usize {
        match self {
            AddrComps::Addrs { a, d, .. } => a / d,
            AddrComps::Bits { ac, .. } => *ac,
        }
    }

    /// Number of cycles `T`.
    pub fn cycles(&self) -> usize {
        match self {
            AddrComps::Addrs { addrs, .. } => addrs.len(),
            AddrComps::Bits { tables, ac } => tables[0].len() >> ac,
        }
    }

    /// The bit tables, converting to [`AddrComps::Bits`] first (for
    /// tests that corrupt a witness).
    pub fn bits_mut(&mut self) -> &mut Vec<Vec<bool>> {
        if let AddrComps::Addrs { .. } = self {
            let ac = self.ac();
            let tables = (0..self.d()).map(|i| self.table(i)).collect();
            *self = AddrComps::Bits { tables, ac };
        }
        match self {
            AddrComps::Bits { tables, .. } => tables,
            AddrComps::Addrs { .. } => unreachable!(),
        }
    }

    /// Component `i` as a dense bit table (index `u + 2^ac * j`).
    pub fn table(&self, i: usize) -> Vec<bool> {
        match self {
            AddrComps::Bits { tables, .. } => tables[i].clone(),
            AddrComps::Addrs { .. } => self.packed(i).to_bools(),
        }
    }

    /// Component `i` as a packed bit table (index `u + 2^ac * j`).
    pub fn packed(&self, i: usize) -> PackedBits {
        match self {
            AddrComps::Bits { tables, .. } => PackedBits::from_bools(&tables[i]),
            AddrComps::Addrs { addrs, .. } => {
                let ac = self.ac();
                let mut out = PackedBits::zero(addrs.len() << ac);
                for (j, &ad) in addrs.iter().enumerate() {
                    out.set(chunk(ad as usize, ac, i) + (j << ac));
                }
                out
            }
        }
    }

    /// The address accessed in cycle `j`. For non-one-hot rows this is
    /// the OR of the set chunks (a cheating witness; any value is fine).
    #[inline]
    pub fn addr(&self, j: usize) -> usize {
        match self {
            AddrComps::Addrs { addrs, .. } => addrs[j] as usize,
            AddrComps::Bits { tables, ac } => {
                let nu = 1usize << ac;
                let mut ad = 0usize;
                for (i, tb) in tables.iter().enumerate() {
                    for u in 0..nu {
                        if tb[u + nu * j] {
                            ad |= u << (i * ac);
                        }
                    }
                }
                ad
            }
        }
    }

    /// All per-cycle addresses (see [`AddrComps::addr`]).
    pub fn addrs(&self) -> std::borrow::Cow<'_, [u32]> {
        match self {
            AddrComps::Addrs { addrs, .. } => std::borrow::Cow::Borrowed(addrs),
            AddrComps::Bits { .. } => (0..self.cycles())
                .map(|j| self.addr(j) as u32)
                .collect::<Vec<_>>()
                .into(),
        }
    }

    /// `Σ_u e[u] · A_i[u + 2^ac j]` for `e = eq_table(r)`, `|r| = ac`:
    /// row `j` of [`partial_eval_rows`].
    #[inline]
    pub(crate) fn row_eval(&self, i: usize, j: usize, e: &[K]) -> K {
        match self {
            AddrComps::Addrs { addrs, .. } => e[chunk(addrs[j] as usize, self.ac(), i)],
            AddrComps::Bits { tables, ac } => {
                let nu = 1usize << ac;
                let mut acc = K::ZERO;
                for (u, &ev) in e.iter().enumerate().take(nu) {
                    if tables[i][u + nu * j] {
                        acc += ev;
                    }
                }
                acc
            }
        }
    }

    /// `f_t~(r_c) = Σ_j eq(r_c, j) · bit_t(addr_j)` for `t < a`: the
    /// address-bit claims of spec 07 §7.4/§7.5 (MLE over cycles).
    pub fn bit_evals(&self, a: usize, r_c: &[K]) -> Vec<K> {
        assert_eq!(
            self.cycles(),
            1 << r_c.len(),
            "bit_evals: wrong cycle count"
        );
        crate::lazy::addr_bit_evals(a, r_c, &|j| self.addr(j))
    }

    /// `ra~(k, r_c) = Σ_j eq(r_c, j) · Π_i A_i(k^(i), j)` for all `k`
    /// (length `2^a`; spec 07 §7.10: a histogram of the addresses).
    pub fn ra_at(&self, a: usize, r_c: &[K]) -> Vec<K> {
        let nk = 1usize << a;
        let t = self.cycles();
        match self {
            AddrComps::Addrs { addrs, .. } => {
                let se = SplitEq::new(r_c);
                let chunks = rayon::current_num_threads().max(1);
                if t >= PAR_THRESHOLD && nk * chunks <= 4 * t {
                    let per = t.div_ceil(chunks);
                    (0..chunks)
                        .into_par_iter()
                        .map(|c| {
                            let mut h = vec![K::ZERO; nk];
                            for j in c * per..((c + 1) * per).min(t) {
                                h[addrs[j] as usize] += se.at(j);
                            }
                            h
                        })
                        .reduce(
                            || vec![K::ZERO; nk],
                            |mut x, y| {
                                for (p, q) in x.iter_mut().zip(&y) {
                                    *p += *q;
                                }
                                x
                            },
                        )
                } else {
                    let mut h = vec![K::ZERO; nk];
                    for (j, &ad) in addrs.iter().enumerate() {
                        h[ad as usize] += se.at(j);
                    }
                    h
                }
            }
            AddrComps::Bits { tables, .. } => {
                let full = full_table(tables, a, tables.len(), t);
                let e = eq_table(r_c);
                (0..nk)
                    .map(|k| {
                        let mut acc = K::ZERO;
                        for (j, &ej) in e.iter().enumerate() {
                            if full[k + nk * j] {
                                acc += ej;
                            }
                        }
                        acc
                    })
                    .collect()
            }
        }
    }
}

#[inline]
fn chunk(addr: usize, ac: usize, i: usize) -> usize {
    (addr >> (i * ac)) & ((1usize << ac) - 1)
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
///
/// `comps` lists the address streams; their components, in order,
/// are the checked components (`names` has one name per component).
/// The sum-check tables (`eq(ρ, j)` and `Ã(r, j)`, `Ã(r', j)` per
/// component) are evaluated per cycle from the addresses and never
/// materialised at full length (§7.10).
pub fn onehot_prove(
    comps: &[&AddrComps],
    names: &[String],
    ac: usize,
    n: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (OneHotProof, Vec<EvalClaim>) {
    let flat: Vec<(&AddrComps, usize)> = comps
        .iter()
        .flat_map(|c| (0..c.d()).map(move |i| (*c, i)))
        .collect();
    assert!(
        flat.iter()
            .all(|(c, _)| c.ac() == ac && c.cycles() == 1 << n),
        "onehot_prove: component shape mismatch"
    );
    let (r, rp, c) = sample_onehot_point(transcript, label, ac);
    let rho = transcript.challenge_ks(&sublabel(label, b"/rho"), n);
    let lam = transcript.challenge_ks(&sublabel(label, b"/lambda"), flat.len());
    let (er, erp, se) = (eq_table(&r), eq_table(&rp), SplitEq::new(&rho));
    let row = |j: usize, out: &mut [K]| {
        out[0] = se.at(j);
        for (x, &(cm, i)) in flat.iter().enumerate() {
            out[1 + 2 * x] = cm.row_eval(i, j, &er);
            out[2 + 2 * x] = cm.row_eval(i, j, &erp);
        }
    };
    let lam_c = lam.clone();
    let combine = move |v: &[K]| onehot_combine(&lam_c, c, v);
    // The honest prover sums its actual tables (0 for valid rows).
    let (_, sc, s, mles) = sumcheck_prove_rows(
        n,
        1 + 2 * flat.len(),
        &row,
        &combine,
        4,
        transcript,
        &sublabel(label, b"/sc"),
    );
    let evals: Vec<Vec<K>> = (0..flat.len())
        .map(|x| vec![mles[1 + 2 * x], mles[2 + 2 * x]])
        .collect();
    let ev_flat: Vec<K> = evals.iter().flatten().copied().collect();
    transcript.absorb_ks(&sublabel(label, b"/evals"), &ev_flat);
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
///
/// The dense prover's tables are one `eq(c_t, ·)` per term and the
/// `d` contracted components per group. Since the summand is linear in
/// the term tables, this prover folds each group's terms into one
/// table `Σ_t ν_t eq(c_t, ·)` (its binding is the same combination of
/// the bound term tables, so every round message is unchanged) and
/// evaluates all tables per cycle from split `eq` tables and the
/// addresses (§7.10).
pub fn virt_prove(
    groups: &[VirtGroup],
    comps_per_group: &[&AddrComps],
    a: usize,
    d: usize,
    n: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (Option<VirtProof>, Vec<EvalClaim>) {
    if d == 1 {
        return (None, virt_direct(groups));
    }
    assert_eq!(groups.len(), comps_per_group.len(), "virt_prove: groups");
    assert!(
        comps_per_group
            .iter()
            .all(|c| c.d() == d && c.ac() == a / d && c.cycles() == 1 << n),
        "virt_prove: component shape mismatch"
    );
    let nterms: usize = groups.iter().map(|g| g.terms.len()).sum();
    let nu = transcript.challenge_ks(&sublabel(label, b"/nu"), nterms);
    // Per group: its terms' (ν_t, split eq(c_t, ·)), and eq_table of
    // each chunk point.
    let mut tpos = 0usize;
    let mut terms: Vec<Vec<(K, SplitEq)>> = Vec::with_capacity(groups.len());
    let mut chunk_eqs: Vec<Vec<Vec<K>>> = Vec::with_capacity(groups.len());
    for g in groups {
        let mut ts = Vec::with_capacity(g.terms.len());
        for term in &g.terms {
            ts.push((nu[tpos], SplitEq::new(&term.cyc)));
            tpos += 1;
        }
        terms.push(ts);
        chunk_eqs.push(
            split_point(&g.r_k, a, d)
                .iter()
                .map(|rc| eq_table(rc))
                .collect(),
        );
    }
    let ng = groups.len();
    // Table layout: one coefficient table per group, then d per group.
    let row = |j: usize, out: &mut [K]| {
        for gi in 0..ng {
            let mut coef = K::ZERO;
            for (nv, se) in &terms[gi] {
                coef += *nv * se.at(j);
            }
            out[gi] = coef;
            for (i, e) in chunk_eqs[gi].iter().enumerate() {
                out[ng + gi * d + i] = comps_per_group[gi].row_eval(i, j, e);
            }
        }
    };
    let combine = move |v: &[K]| {
        let mut acc = K::ZERO;
        for gi in 0..ng {
            let mut prod = v[gi];
            for i in 0..d {
                prod *= v[ng + gi * d + i];
            }
            acc += prod;
        }
        acc
    };
    // The honest prover sums the actual tables (not the claimed value).
    let (_, sc, s, mles) = sumcheck_prove_rows(
        n,
        ng * (1 + d),
        &row,
        &combine,
        d + 1,
        transcript,
        &sublabel(label, b"/sc"),
    );
    let evals = mles[ng..].to_vec();
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
