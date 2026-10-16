//! The Spartan family (spec 06 §6.3–6.8). Mirrors
//! `reference/openmagnetar/spartan.py` byte for byte in its transcript
//! interaction.
//!
//! One code path covers Construction 1 / SIMD / BinarySpartan (`T = 1`
//! relation, no layout) and Construction 2, Virtual Spartan (`T = 2`
//! relations, segment layout, optional cross-step). Every transcript
//! label is `P ‖ "/" ‖ …` for the caller-supplied prefix `P` (`b"vsp"`
//! in the full protocol and in the reference tests, per spec 06 §6.3).
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - The witness `W` is `&[Vec<bool>]` and the public inputs `X` are
//!   `&[Vec<K>]`; Python's mixed `0`/`1`-int-or-`K` entries are
//!   converted by the caller ([`K::from_bit`]).
//! - Python `ValueError`s in [`prove`] (and from [`check_layout`],
//!   including inside [`verify`]) **panic**; `VerificationError` is
//!   returned as `Err` from [`verify`]. The prover-side `VerificationError`s
//!   of Python's cross-step setup likewise panic in [`prove`].
//! - The claim type is [`Claim`], re-exported from `om-mosaic`
//!   (Python's `spartan.py` imports `Claim` from `mosaic.py`); the
//!   whole-`W` claim of the no-layout mode keeps Python's sentinel
//!   `comp_id = -1`, hence `i64` ids.

use om_field::K;
use om_sumcheck::{
    SumcheckProof, VerificationError, bind_low_in_place, eq_eval, eq_table, interpolate_eval,
    mle_eval, mle_eval_bits, sumcheck_init, sumcheck_prove, sumcheck_round_evals, sumcheck_verify,
};
use om_transcript::{Transcript, u64le};
use rayon::prelude::*;

use std::sync::atomic::{AtomicBool, Ordering};

use om_sumcheck::PackedBits;

use crate::r1cs::{BitRow, R1CS, check_witness_bits, simd_satisfied};

/// An evaluation claim `p~_{comp_id}(point) = value` on a component
/// polynomial (Python `mosaic.Claim`, re-exported from `om-mosaic`;
/// `comp_id = -1` denotes the whole witness matrix `W` in the
/// no-layout mode).
pub use om_mosaic::Claim;

/// What a column segment is handed to (spec 06 §6.5; Python's
/// `"direct"` / `"virtual"` / `"pad"`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SegmentKind {
    Direct,
    Virtual,
    Pad,
}

impl SegmentKind {
    /// The Python / vector spelling of this kind.
    pub fn as_str(self) -> &'static str {
        match self {
            SegmentKind::Direct => "direct",
            SegmentKind::Virtual => "virtual",
            SegmentKind::Pad => "pad",
        }
    }

    /// Parse the Python / vector spelling, if it is one of the three.
    pub fn from_name(s: &str) -> Option<Self> {
        match s {
            "direct" => Some(SegmentKind::Direct),
            "virtual" => Some(SegmentKind::Virtual),
            "pad" => Some(SegmentKind::Pad),
            _ => None,
        }
    }
}

/// A column segment of `W`: columns
/// `[block * 2^log_cols, (block+1) * 2^log_cols)` (spec 06 §6.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Segment {
    pub seg_id: i64,
    pub kind: SegmentKind,
    pub log_cols: usize,
    pub block: usize,
}

/// The cross-step designation (spec 06 §6.6): whole segments `in_id`
/// and `out_id` of equal size `2^lam`, with public bit-vector boundary
/// states `init` and `fin` of length `2^lam`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossStep {
    pub in_id: i64,
    pub out_id: i64,
    pub init: Vec<bool>,
    pub fin: Vec<bool>,
}

/// A Spartan proof (field order as in spec 06 §6.7).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpartanProof {
    /// `[t][round] -> [g(t_0), g(t_2), g(t_3)]`, `rho + s` rounds each.
    pub outer_msgs: Vec<Vec<Vec<K>>>,
    /// `[t] -> [v_A, v_B, v_C]`.
    pub outer_finals: Vec<Vec<K>>,
    pub inner: SumcheckProof,
    pub v_w: K,
    /// One per non-pad segment, in layout order.
    pub seg_vals: Vec<K>,
    pub xs_proof: Option<SumcheckProof>,
    /// `[v_in, v_out]`.
    pub xs_vals: Option<Vec<K>>,
}

fn lbl(p: &[u8], parts: &[&[u8]]) -> Vec<u8> {
    let mut out = p.to_vec();
    for part in parts {
        out.push(b'/');
        out.extend_from_slice(part);
    }
    out
}

fn bits_of(v: usize, n: usize) -> Vec<K> {
    (0..n).map(|k| K::from_bit((v >> k) & 1 == 1)).collect()
}

/// Validate a segment layout (spec 06 §6.5): kind well-formed by
/// construction, ids distinct, each segment inside `[0, 2^(nu-1))`,
/// pairwise disjoint.
///
/// # Panics
/// Panics on an invalid layout (Python raises `ValueError`).
pub fn check_layout(segs: &[Segment], nu: usize) {
    assert!(nu >= 1, "nu must be at least 1");
    let cols = 1usize << (nu - 1);
    let mut used: Vec<(i64, usize, usize)> = Vec::new();
    for s in segs {
        assert!(
            used.iter().all(|&(id, _, _)| id != s.seg_id),
            "duplicate segment id"
        );
        assert!(s.log_cols < nu, "segment out of range");
        let (lo, hi) = (s.block << s.log_cols, (s.block + 1) << s.log_cols);
        assert!(hi <= cols, "segment out of range");
        for &(_, a, b) in &used {
            assert!(!(lo < b && a < hi), "segments overlap");
        }
        used.push((s.seg_id, lo, hi));
    }
}

/// The MLE of the `next` indicator `N(a, b) = [int(b) = int(a)+1 and
/// int(a) < 2^s - 1]`, LSB-first (C2), `s = a.len()`:
/// `N~ = sum_i [prod_{j<i} a_j (1+b_j)] (1+a_i) b_i [prod_{j>i} eq_j]`
/// (spec 06 §6.6). For `s = 0` this is `0`.
///
/// # Panics
/// Panics if `a.len() != b.len()` (Python raises `IndexError`).
pub fn next_mle(a: &[K], b: &[K]) -> K {
    assert_eq!(a.len(), b.len(), "next_mle: length mismatch");
    let s = a.len();
    let mut suffix = vec![K::ONE; s + 1];
    for j in (0..s).rev() {
        suffix[j] = suffix[j + 1] * (K::ONE + a[j] + b[j]);
    }
    let (mut acc, mut prefix) = (K::ZERO, K::ONE);
    for i in 0..s {
        acc += prefix * (K::ONE + a[i]) * b[i] * suffix[i + 1];
        prefix *= a[i] * (K::ONE + b[i]);
    }
    acc
}

/// The values at `r_u` of the MLEs of the public `u`-tables `a_out`,
/// `a_in` of the cross-step sum-check (spec 06 §6.6 step 4):
/// `(A_out, A_in)`.
pub fn xs_weights(tau_u: &[K], gamma: K, r_u: &[K]) -> (K, K) {
    let (mut prod_tau, mut prod_r, mut prod_nr) = (K::ONE, K::ONE, K::ONE);
    for (&t, &r) in tau_u.iter().zip(r_u) {
        prod_tau *= t;
        prod_r *= r;
        prod_nr *= K::ONE + r;
    }
    let a_out = eq_eval(tau_u, r_u) + prod_tau * prod_r + gamma * gamma * prod_r;
    let a_in = next_mle(tau_u, r_u) + gamma * prod_nr;
    (a_out, a_in)
}

/// The flat bit table of one segment over all instances:
/// index = local column + `2^log_cols` * instance (Python
/// `spartan._segment_table`, also used by `protocol.py`).
pub fn segment_table<R: BitRow>(w: &[R], sg: &Segment) -> Vec<bool> {
    let (off, n) = (sg.block << sg.log_cols, 1usize << sg.log_cols);
    w.iter()
        .flat_map(|row| (0..n).map(move |y| row.bit(off + y)))
        .collect()
}

/// [`segment_table`] in packed form: the same bits, eight times
/// smaller, never expanded to a bool table.
pub fn segment_table_packed<R: BitRow>(w: &[R], sg: &Segment) -> PackedBits {
    let (off, n) = (sg.block << sg.log_cols, 1usize << sg.log_cols);
    let mut out = PackedBits::zero(w.len() * n);
    if w.first().and_then(|r| r.packed_words()).is_some() {
        if n >= 64 && off.is_multiple_of(64) {
            let wpr = n / 64;
            let src_off = off / 64;
            out.words_mut()
                .par_chunks_mut(wpr)
                .zip(w.par_iter())
                .for_each(|(dst, row)| {
                    let src = row.packed_words().expect("packed_words");
                    dst.copy_from_slice(&src[src_off..src_off + wpr]);
                });
            return out;
        } else if n > 0 && n < 64 && 64usize.is_multiple_of(n) && off.is_multiple_of(n) {
            let rows_per_word = 64 / n;
            let src_wi = off / 64;
            let src_shift = off % 64;
            let mask = (1u64 << n) - 1;
            out.words_mut()
                .par_iter_mut()
                .enumerate()
                .for_each(|(wi, dst_word)| {
                    let u_start = wi * rows_per_word;
                    let u_end = (u_start + rows_per_word).min(w.len());
                    let mut acc = 0u64;
                    for (k, row) in w[u_start..u_end].iter().enumerate() {
                        let src = row.packed_words().expect("packed_words");
                        let bits = (src[src_wi] >> src_shift) & mask;
                        acc |= bits << (k * n);
                    }
                    *dst_word = acc;
                });
            return out;
        }
    }
    for (u, row) in w.iter().enumerate() {
        for y in 0..n {
            if row.bit(off + y) {
                out.set(y + n * u);
            }
        }
    }
    out
}

/// `g(t) = sum_i E(t)(A(t)B(t) + C(t))` at `t_0..t_3`, where
/// `T(t) = T[2i] + t (T[2i] + T[2i+1])`.
fn g_evals(e: &[K], a: &[K], b: &[K], c: &[K]) -> [K; 4] {
    let half = e.len() / 2;
    let add_i = |acc: &mut [K; 4], i: usize| {
        let (e0, e1) = (e[2 * i], e[2 * i + 1]);
        let (a0, a1) = (a[2 * i], a[2 * i + 1]);
        let (b0, b1) = (b[2 * i], b[2 * i + 1]);
        let (c0, c1) = (c[2 * i], c[2 * i + 1]);
        let p0 = a0 * b0 + c0;
        let p1 = a1 * b1 + c1;
        let p2 = (a0 + a1) * (b0 + b1);
        let p_mid = p0 + p1 + p2;
        let px = p0 + p_mid.mul_x() + p2.mul_x().mul_x();
        let px1 = px + p0 + p1;
        let de = e0 + e1;
        let ex = e0 + de.mul_x();
        let ex1 = ex + de;
        acc[0] += e0 * p0;
        acc[1] += e1 * p1;
        acc[2] += ex * px;
        acc[3] += ex1 * px1;
    };
    // Each slot is a XOR-sum over `i`, so a parallel reduction is exact.
    if e.len() >= 1 << 14 {
        (0..half)
            .into_par_iter()
            .fold(
                || [K::ZERO; 4],
                |mut acc, i| {
                    add_i(&mut acc, i);
                    acc
                },
            )
            .reduce(
                || [K::ZERO; 4],
                |mut x, y| {
                    for (s, v) in x.iter_mut().zip(y) {
                        *s += v;
                    }
                    x
                },
            )
    } else {
        let mut acc = [K::ZERO; 4];
        for i in 0..half {
            add_i(&mut acc, i);
        }
        acc
    }
}

fn default_names(t: usize) -> Vec<Vec<u8>> {
    if t <= 2 {
        [b"bin".to_vec(), b"fld".to_vec()][..t].to_vec()
    } else {
        (0..t).map(|i| format!("r{i}").into_bytes()).collect()
    }
}

fn resolve_names(names: Option<&[Vec<u8>]>, t: usize) -> Vec<Vec<u8>> {
    match names {
        Some(n) if !n.is_empty() => n.to_vec(),
        _ => default_names(t),
    }
}

/// Steps 0–1: absorb the shape and the public inputs, squeeze `tau_t`
/// per relation.
#[allow(clippy::too_many_arguments)]
fn setup(
    transcript: &mut Transcript,
    p: &[u8],
    t: usize,
    rho: usize,
    nu: usize,
    s: usize,
    nx: usize,
    x: &[Vec<K>],
    names: &[Vec<u8>],
) -> Vec<Vec<K>> {
    let mut shape = Vec::with_capacity(40);
    for v in [t, rho, nu, s, nx] {
        shape.extend_from_slice(&u64le(v as u64));
    }
    transcript.absorb_bytes(&lbl(p, &[b"shape"]), &shape);
    let flat: Vec<K> = x.iter().flat_map(|row| row.iter().copied()).collect();
    transcript.absorb_ks(&lbl(p, &[b"pub"]), &flat);
    names
        .iter()
        .map(|nm| transcript.challenge_ks(&lbl(p, &[b"tau", nm]), rho + s))
        .collect()
}

/// `PF = sum_u eq(r_inst, u) (1, x_u)`, a table of length `2^(nu-1)`
/// (spec 06 §6.1).
///
/// Only the non-zero entries `(1, x_u)` are visited (the verifier's
/// public inputs are short), so the cost is `O(q · (1 + |x_u|))`
/// rather than `O(q · 2^(nu-1))`.
fn fold_public(x: &[Vec<K>], nu: usize, r_inst: &[K]) -> Vec<K> {
    fold_public_sparse(x, nu, &eq_table(r_inst))
}

// -----------------------------------------------------------------
// Sparse outer phase. The dense prover materialises, per relation,
// four tables of `q * 2^rho` field elements. Here the `rho` row
// rounds instead stream over instances: each relation's matrices are
// kept as sparse rows folded by the row challenges seen so far, and
// an instance's bound `Az`, `Bz`, `Cz` tables are computed from the
// folded matrices and its witness row on demand, then dropped. The
// `eq` table factors as `eq_row(row) * eq_inst(inst)`, so a round's
// evaluations are the eq_inst-weighted sum over instances of the
// per-instance evaluations. After the row rounds, one scalar per
// instance and matrix remains, and the `s` instance rounds run
// densely on tables of length `q`. Transcript and proof bytes are
// identical to the dense definition.

/// One sparse matrix as rows of `(column, coefficient)` lists.
type SparseRows = Vec<Vec<(usize, K)>>;

const PAR_THRESHOLD: usize = 1 << 14;

fn sparse_rows(mat: &crate::r1cs::SparseMatrix) -> SparseRows {
    let mut rows: SparseRows = vec![Vec::new(); 1 << mat.rho];
    for &(r, c, v) in mat.entries() {
        rows[r].push((c, v));
    }
    rows
}

/// Fold sparse rows by one row challenge: new row `i` is
/// `(1 + r) * row[2i] + r * row[2i+1]` merged by column.
fn fold_sparse_rows(rows: SparseRows, r: K) -> SparseRows {
    let (c0, c1) = (K::ONE + r, r);
    let fold_pair = |pair: &[Vec<(usize, K)>]| -> Vec<(usize, K)> {
        let (l, rr) = (&pair[0], &pair[1]);
        if l.is_empty() && rr.is_empty() {
            return Vec::new();
        }
        let mut out: Vec<(usize, K)> = Vec::with_capacity(l.len() + rr.len());
        let (mut a, mut b) = (0, 0);
        while a < l.len() && b < rr.len() {
            match l[a].0.cmp(&rr[b].0) {
                core::cmp::Ordering::Less => {
                    out.push((l[a].0, c0 * l[a].1));
                    a += 1;
                }
                core::cmp::Ordering::Greater => {
                    out.push((rr[b].0, c1 * rr[b].1));
                    b += 1;
                }
                core::cmp::Ordering::Equal => {
                    let v = c0 * l[a].1 + c1 * rr[b].1;
                    if !v.is_zero() {
                        out.push((l[a].0, v));
                    }
                    a += 1;
                    b += 1;
                }
            }
        }
        out.extend(l[a..].iter().map(|&(c, v)| (c, c0 * v)));
        out.extend(rr[b..].iter().map(|&(c, v)| (c, c1 * v)));
        out
    };
    if rows.len() >= PAR_THRESHOLD {
        rows.par_chunks(2).map(fold_pair).collect()
    } else {
        rows.chunks(2).map(fold_pair).collect()
    }
}

/// `z[col]` for instance `(w_row, x_row)` without building `z`
/// (`build_z` layout: `w`, then `1`, then `x`, then zeros).
fn z_at<R: BitRow>(w_row: &R, x_row: &[K], half: usize, col: usize) -> K {
    if col < half {
        K::from_bit(w_row.bit(col))
    } else if col == half {
        K::ONE
    } else {
        x_row.get(col - half - 1).copied().unwrap_or(K::ZERO)
    }
}

/// One relation in the sparse row phase.
struct OuterRel {
    /// Folded sparse rows of `(A, B, C)`.
    mats: [SparseRows; 3],
    /// Bound `eq(tau_row, .)` table over the remaining row variables.
    eq_row: Vec<K>,
    /// `eq(tau_inst, u)` per instance.
    eq_inst: Vec<K>,
}

/// `W~(., r_inst)` as a column table: `sum_u eq(r_inst, u) W[u][c]`
/// for `c < half`, given `eqi = eq(r_inst, .)`. Instances are folded
/// in parallel chunks; each slot is a XOR-sum, so the result is exact.
fn fold_witness<R: BitRow>(w: &[R], eqi: &[K], half: usize) -> Vec<K> {
    let chunk = w.len().div_ceil(4 * rayon::current_num_threads()).max(1);
    w.par_chunks(chunk)
        .zip(eqi.par_chunks(chunk))
        .map(|(ws, es)| {
            let mut acc = vec![K::ZERO; half];
            for (wu, &e) in ws.iter().zip(es) {
                wu.for_each_one(|c| acc[c] += e);
            }
            acc
        })
        .reduce(
            || vec![K::ZERO; half],
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(&b) {
                    *x += *y;
                }
                a
            },
        )
}

/// [`fold_public`] from the instance `eq` table, touching only the
/// non-zero entries `(1, x_u)` of each public part. Same values: the
/// skipped terms are `eq * 0`.
fn fold_public_sparse(x: &[Vec<K>], nu: usize, eqi: &[K]) -> Vec<K> {
    let half = 1usize << (nu - 1);
    let mut out = vec![K::ZERO; half];
    for (u, xu) in x.iter().enumerate() {
        assert!(xu.len() < half, "public input too long");
        out[0] += eqi[u];
        for (slot, &v) in out[1..].iter_mut().zip(xu) {
            *slot += eqi[u] * v;
        }
    }
    out
}

/// One sparse row compiled for fast bit/word evaluation over `z = (w, 1, x)`.
struct CompiledRow {
    /// `(word_idx, bit_mask)` for `col < half` where `coef == K::ONE`.
    ones_masks: Vec<(usize, u64)>,
    /// `(word_idx, shift, mask, base_coef)` for consecutive columns in one word
    /// where `coef[j] == base_coef * X^j`.
    geom_runs: Vec<(usize, u32, u64, K)>,
    /// Remaining `(word_idx, bit_mask, coef)` with `col < half` and `coef != K::ONE`.
    other_w: Vec<(usize, u64, K)>,
    /// Coefficient at `col == half` (where `z[half] == 1`).
    const_term: K,
    /// Entries `(col - half - 1, coef)` for `col > half`.
    pub_terms: Vec<(usize, K)>,
}

impl CompiledRow {
    fn from_entries(entries: &[(usize, K)], half: usize) -> Self {
        let mut ones_masks: Vec<(usize, u64)> = Vec::new();
        let mut geom_runs: Vec<(usize, u32, u64, K)> = Vec::new();
        let mut other_w: Vec<(usize, u64, K)> = Vec::new();
        let mut const_term = K::ZERO;
        let mut pub_terms: Vec<(usize, K)> = Vec::new();

        let mut idx = 0;
        while idx < entries.len() {
            let (col, coef) = entries[idx];
            if col == half {
                const_term += coef;
                idx += 1;
                continue;
            }
            if col > half {
                pub_terms.push((col - half - 1, coef));
                idx += 1;
                continue;
            }
            let wi = col / 64;
            let shift = (col % 64) as u32;
            let mut len = 1usize;
            let mut prev = coef;
            while idx + len < entries.len() {
                let (nc, ncoef) = entries[idx + len];
                if nc != col + len || nc >= half || nc / 64 != wi {
                    break;
                }
                let expected = prev.mul_x();
                if ncoef != expected {
                    break;
                }
                prev = expected;
                len += 1;
            }
            if len >= 2 {
                let mask = if len == 64 {
                    u64::MAX
                } else {
                    (1u64 << len) - 1
                };
                geom_runs.push((wi, shift, mask, coef));
                idx += len;
            } else {
                let bit = 1u64 << shift;
                if coef.is_one() {
                    if let Some(last) = ones_masks.last_mut().filter(|(w, _)| *w == wi) {
                        last.1 |= bit;
                    } else {
                        ones_masks.push((wi, bit));
                    }
                } else if let Some(last) = other_w
                    .last_mut()
                    .filter(|(w, _, c)| *w == wi && *c == coef)
                {
                    last.1 |= bit;
                } else {
                    other_w.push((wi, bit, coef));
                }
                idx += 1;
            }
        }
        CompiledRow {
            ones_masks,
            geom_runs,
            other_w,
            const_term,
            pub_terms,
        }
    }

    #[inline(always)]
    fn eval_words(&self, words: &[u64], x_row: &[K]) -> K {
        let mut v = self.const_term;
        let mut parity = 0u32;
        for &(wi, mask) in &self.ones_masks {
            parity ^= (words[wi] & mask).count_ones();
        }
        if parity & 1 != 0 {
            v += K::ONE;
        }
        for &(wi, shift, mask, base_coef) in &self.geom_runs {
            let bits = (words[wi] >> shift) & mask;
            if bits != 0 {
                let kb = K::from_u128(u128::from(bits));
                v += if base_coef.is_one() {
                    kb
                } else {
                    kb * base_coef
                };
            }
        }
        for &(wi, mask, coef) in &self.other_w {
            if (words[wi] & mask).count_ones() & 1 != 0 {
                v += coef;
            }
        }
        for &(xi, coef) in &self.pub_terms {
            if let Some(&xv) = x_row.get(xi)
                && !xv.is_zero()
            {
                v += coef * xv;
            }
        }
        v
    }
}

#[inline]
fn eval_sparse_row<R: BitRow>(
    entries: &[(usize, K)],
    compiled: &CompiledRow,
    w_row: &R,
    x_row: &[K],
    half: usize,
) -> K {
    if let Some(words) = w_row.packed_words() {
        return compiled.eval_words(words, x_row);
    }
    let mut v = K::ZERO;
    for &(col, coef) in entries {
        if col < half {
            if w_row.bit(col) {
                v += coef;
            }
        } else {
            let zv = z_at(w_row, x_row, half, col);
            if !zv.is_zero() {
                v += coef * zv;
            }
        }
    }
    v
}

/// The value at `r_col[..log_cols] || r_inst` of every non-pad
/// segment's MLE (in layout order), computed directly from the
/// already-folded witness column table `wfold[c] = sum_u eqi[u] W[u][c]`.
fn segment_values(wfold: &[K], segs: &[Segment], r_col: &[K]) -> Vec<K> {
    segs.iter()
        .filter(|sg| sg.kind != SegmentKind::Pad)
        .map(|sg| {
            let off = sg.block << sg.log_cols;
            let n = 1usize << sg.log_cols;
            mle_eval(&wfold[off..off + n], &r_col[..sg.log_cols])
        })
        .collect()
}

/// The Spartan prover (spec 06 §6.3, 6.5, 6.6). Returns
/// `(proof, claims)`. `unchecked` skips the satisfiability check (and
/// the outer-claim check); it exists for negative tests only, as in
/// Python.
///
/// # Panics
/// Panics where Python raises `ValueError`: no relations; relations not
/// sharing `(rho, nu)`; instance count not a power of two; `W`/`X` row
/// counts differing; malformed witness rows; witness not satisfying
/// the SIMD R1CS (unless `unchecked`); public inputs of unequal
/// length; invalid layout; invalid cross-step designation.
#[allow(clippy::too_many_arguments)]
pub fn prove<R: BitRow>(
    rels: &[R1CS],
    w: &[R],
    x: &[Vec<K>],
    transcript: &mut Transcript,
    p: &[u8],
    names: Option<&[Vec<u8>]>,
    segments: Option<&[Segment]>,
    cross: Option<&CrossStep>,
    unchecked: bool,
) -> (SpartanProof, Vec<Claim>) {
    let t = rels.len();
    let names = resolve_names(names, t);
    let (rho, nu) = {
        let first = rels.first().expect("no relations");
        (first.rho, first.nu)
    };
    assert!(
        rels.iter().all(|r| (r.rho, r.nu) == (rho, nu)),
        "relations must share (rho, nu)"
    );
    let q = w.len();
    assert!(
        q.is_power_of_two(),
        "number of instances must be a power of two"
    );
    let s = q.trailing_zeros() as usize;
    assert_eq!(x.len(), q, "W and X must have one row per instance");
    check_witness_bits(w, nu);
    // With row rounds, the satisfiability check rides along the first
    // row round (which computes every instance's `Az`, `Bz`, `Cz` rows
    // anyway); without them it runs here.
    if !unchecked && rho == 0 {
        assert!(
            simd_satisfied(rels, w, x),
            "witness does not satisfy the SIMD R1CS"
        );
    }
    let nx = x[0].len();
    assert!(
        x.iter().all(|xi| xi.len() == nx),
        "public inputs must have equal length"
    );
    if let Some(segs) = segments {
        check_layout(segs, nu);
    }

    let tau = setup(transcript, p, t, rho, nu, s, nx, x, &names);

    // Sparse row phase: stream instances against folded sparse
    // matrices (see the note above `OuterRel`). No table of
    // `q * 2^rho` field elements is materialised.
    let half = 1usize << (nu - 1);
    let mut orels: Vec<OuterRel> = rels
        .iter()
        .enumerate()
        .map(|(ti, rel)| OuterRel {
            mats: [
                sparse_rows(&rel.a),
                sparse_rows(&rel.b),
                sparse_rows(&rel.c),
            ],
            eq_row: eq_table(&tau[ti][..rho]),
            eq_inst: eq_table(&tau[ti][rho..]),
        })
        .collect();
    let mut msgs: Vec<Vec<Vec<K>>> = vec![Vec::new(); t];
    let mut r_row: Vec<Vec<K>> = vec![Vec::new(); t];
    let mut r_inst: Vec<K> = Vec::new();
    let unsatisfied = AtomicBool::new(false);
    for round in 0..rho {
        // Identify active row pairs `i` where at least one of the three
        // matrices has a non-empty row at `2i` or `2i+1` and compile
        // only those active pairs in parallel.
        let check = round == 0 && !unchecked;
        let compiled: Vec<(Vec<usize>, Vec<[CompiledRow; 6]>)> = orels
            .iter()
            .map(|orel| {
                let half_rows = orel.eq_row.len() / 2;
                let is_active = |&i: &usize| {
                    !orel.mats[0][2 * i].is_empty()
                        || !orel.mats[0][2 * i + 1].is_empty()
                        || !orel.mats[1][2 * i].is_empty()
                        || !orel.mats[1][2 * i + 1].is_empty()
                        || !orel.mats[2][2 * i].is_empty()
                        || !orel.mats[2][2 * i + 1].is_empty()
                };
                let active: Vec<usize> = if half_rows >= PAR_THRESHOLD {
                    (0..half_rows).into_par_iter().filter(is_active).collect()
                } else {
                    (0..half_rows).filter(is_active).collect()
                };
                let compile_pair = |&i: &usize| -> [CompiledRow; 6] {
                    let (r0, r1) = (2 * i, 2 * i + 1);
                    [
                        CompiledRow::from_entries(&orel.mats[0][r0], half),
                        CompiledRow::from_entries(&orel.mats[0][r1], half),
                        CompiledRow::from_entries(&orel.mats[1][r0], half),
                        CompiledRow::from_entries(&orel.mats[1][r1], half),
                        CompiledRow::from_entries(&orel.mats[2][r0], half),
                        CompiledRow::from_entries(&orel.mats[2][r1], half),
                    ]
                };
                let cmats: Vec<[CompiledRow; 6]> = if active.len() >= PAR_THRESHOLD {
                    active.par_iter().map(compile_pair).collect()
                } else {
                    active.iter().map(compile_pair).collect()
                };
                (active, cmats)
            })
            .collect();

        // Stream each instance `u` across the active row pairs so `w[u]`
        // stays hot in L1/L2 cache; multiply by `eq_row` once after the
        // instance reduction.
        let init_sums = || -> Vec<Vec<[K; 3]>> {
            compiled
                .iter()
                .map(|(active, _)| vec![[K::ZERO; 3]; active.len()])
                .collect()
        };
        let chunk = q.div_ceil(4 * rayon::current_num_threads()).max(1);
        let pair_sums: Vec<Vec<[K; 3]>> = (0..q)
            .into_par_iter()
            .chunks(chunk)
            .map(|us| {
                let mut acc = init_sums();
                for u in us {
                    let wu = &w[u];
                    let xu = &x[u];
                    for (ti, (orel, (active, cmats))) in orels.iter().zip(&compiled).enumerate() {
                        let equ = orel.eq_inst[u];
                        let rel_acc = &mut acc[ti];
                        for (k_idx, (&i, cm)) in active.iter().zip(cmats).enumerate() {
                            let (r0, r1) = (2 * i, 2 * i + 1);
                            let a0 = eval_sparse_row(&orel.mats[0][r0], &cm[0], wu, xu, half);
                            let a1 = eval_sparse_row(&orel.mats[0][r1], &cm[1], wu, xu, half);
                            let b0 = eval_sparse_row(&orel.mats[1][r0], &cm[2], wu, xu, half);
                            let b1 = eval_sparse_row(&orel.mats[1][r1], &cm[3], wu, xu, half);
                            let c0 = eval_sparse_row(&orel.mats[2][r0], &cm[4], wu, xu, half);
                            let c1 = eval_sparse_row(&orel.mats[2][r1], &cm[5], wu, xu, half);
                            let p0 = a0 * b0 + c0;
                            let p1 = a1 * b1 + c1;
                            if check && (!p0.is_zero() || !p1.is_zero()) {
                                unsatisfied.store(true, Ordering::Relaxed);
                            }
                            let p2 = (a0 + a1) * (b0 + b1);
                            let slot = &mut rel_acc[k_idx];
                            if !p0.is_zero() {
                                slot[0] += if p0.is_one() { equ } else { equ * p0 };
                            }
                            if !p1.is_zero() {
                                slot[1] += if p1.is_one() { equ } else { equ * p1 };
                            }
                            if !p2.is_zero() {
                                slot[2] += if p2.is_one() { equ } else { equ * p2 };
                            }
                        }
                    }
                }
                acc
            })
            .reduce(init_sums, |mut a, b| {
                for (ra, rb) in a.iter_mut().zip(&b) {
                    for (sa, sb) in ra.iter_mut().zip(rb) {
                        sa[0] += sb[0];
                        sa[1] += sb[1];
                        sa[2] += sb[2];
                    }
                }
                a
            });

        let mut evs = vec![[K::ZERO; 4]; t];
        for (ti, (orel, (active, _))) in orels.iter().zip(&compiled).enumerate() {
            for (k_idx, &i) in active.iter().enumerate() {
                let [s0, s1, s2] = pair_sums[ti][k_idx];
                let (e0, e1) = (orel.eq_row[2 * i], orel.eq_row[2 * i + 1]);
                let s_mid = s0 + s1 + s2;
                let px = s0 + s_mid.mul_x() + s2.mul_x().mul_x();
                let px1 = px + s0 + s1;
                let de = e0 + e1;
                let ex = e0 + de.mul_x();
                let ex1 = ex + de;
                evs[ti][0] += e0 * s0;
                evs[ti][1] += e1 * s1;
                evs[ti][2] += ex * px;
                evs[ti][3] += ex1 * px1;
            }
        }

        if check {
            assert!(
                !unsatisfied.load(Ordering::Relaxed),
                "witness does not satisfy the SIMD R1CS"
            );
            for ev in &evs {
                assert!(ev[0] + ev[1] == K::ZERO, "outer claim is non-zero");
            }
        }
        for ti in 0..t {
            let msg = vec![evs[ti][0], evs[ti][2], evs[ti][3]];
            transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"msg"]), &msg);
            let r = transcript.challenge_k(&lbl(p, &[b"outer", &names[ti], b"row"]));
            msgs[ti].push(msg);
            r_row[ti].push(r);
            bind_low_in_place(&mut orels[ti].eq_row, r);
            let mats = std::mem::take(&mut orels[ti].mats);
            orels[ti].mats = mats.map(|rows| fold_sparse_rows(rows, r));
        }
    }
    // Instance phase tables: one scalar per instance and matrix.
    let mut tabs: Vec<[Vec<K>; 4]> = Vec::with_capacity(t);
    for orel in &orels {
        let c0 = CompiledRow::from_entries(&orel.mats[0][0], half);
        let c1 = CompiledRow::from_entries(&orel.mats[1][0], half);
        let c2 = CompiledRow::from_entries(&orel.mats[2][0], half);
        let eval_col = |entries: &[(usize, K)], comp: &CompiledRow| -> Vec<K> {
            if q >= 1 << 12 {
                (0..q)
                    .into_par_iter()
                    .map(|u| eval_sparse_row(entries, comp, &w[u], &x[u], half))
                    .collect()
            } else {
                (0..q)
                    .map(|u| eval_sparse_row(entries, comp, &w[u], &x[u], half))
                    .collect()
            }
        };
        let e0 = orel.eq_row[0];
        let eq0 = if q >= 1 << 14 {
            orel.eq_inst.par_iter().map(|&e| e0 * e).collect()
        } else {
            orel.eq_inst.iter().map(|&e| e0 * e).collect()
        };
        tabs.push([
            eq0,
            eval_col(&orel.mats[0][0], &c0),
            eval_col(&orel.mats[1][0], &c1),
            eval_col(&orel.mats[2][0], &c2),
        ]);
    }
    if rho == 0 && !unchecked {
        for tab in &tabs {
            let total = (0..q).fold(K::ZERO, |acc, i| {
                acc + tab[0][i] * (tab[1][i] * tab[2][i] + tab[3][i])
            });
            assert!(total == K::ZERO, "outer claim is non-zero");
        }
    }
    for _ in 0..s {
        let evs: Vec<[K; 4]> = (0..t)
            .map(|ti| g_evals(&tabs[ti][0], &tabs[ti][1], &tabs[ti][2], &tabs[ti][3]))
            .collect();
        for ti in 0..t {
            let msg = vec![evs[ti][0], evs[ti][2], evs[ti][3]];
            transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"msg"]), &msg);
            msgs[ti].push(msg);
        }
        let r = transcript.challenge_k(&lbl(p, &[b"outer", b"inst"]));
        r_inst.push(r);
        for tab in &mut tabs {
            for t in tab.iter_mut() {
                bind_low_in_place(t, r);
            }
        }
    }
    let finals: Vec<Vec<K>> = (0..t)
        .map(|ti| vec![tabs[ti][1][0], tabs[ti][2][0], tabs[ti][3][0]])
        .collect();
    drop(tabs);
    for ti in 0..t {
        transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"final"]), &finals[ti]);
    }
    let alpha = transcript.challenge_ks(&lbl(p, &[b"alpha"]), 3 * t);

    // Inner sum-check over columns: `orel.mats[m][0]` already holds the
    // sparse entries of `M~(r_row, .)` after folding all `rho` row rounds.
    let mut v_star = K::ZERO;
    let mut mcomb = vec![K::ZERO; 1 << nu];
    for (ti, orel) in orels.iter().enumerate() {
        for m in 0..3 {
            let a = alpha[3 * ti + m];
            v_star += a * finals[ti][m];
            for &(c, v) in &orel.mats[m][0] {
                mcomb[c] += a * v;
            }
        }
    }
    drop(orels);
    let eqi = eq_table(&r_inst);
    let wfold = fold_witness(w, &eqi, half);
    let mut zfold = wfold.clone();
    zfold.extend(fold_public_sparse(x, nu, &eqi));
    let (inner, r_y, _) = sumcheck_prove(
        v_star,
        vec![mcomb, zfold],
        &|v: &[K]| v[0] * v[1],
        2,
        transcript,
        &lbl(p, &[b"inner"]),
    );
    let r_col: Vec<K> = r_y[..nu - 1].to_vec();
    let v_w = mle_eval(&wfold, &r_col);
    transcript.absorb_k(&lbl(p, &[b"vw"]), v_w);

    let mut claims: Vec<Claim> = Vec::new();
    let mut seg_vals: Vec<K> = Vec::new();
    match segments {
        None => {
            let mut point = r_col.clone();
            point.extend_from_slice(&r_inst);
            claims.push(Claim {
                comp_id: -1,
                point,
                value: v_w,
            });
        }
        Some(segs) => {
            let vals = segment_values(&wfold, segs, &r_col);
            for (sg, v) in segs
                .iter()
                .filter(|sg| sg.kind != SegmentKind::Pad)
                .zip(vals)
            {
                let mut point: Vec<K> = r_col[..sg.log_cols].to_vec();
                point.extend_from_slice(&r_inst);
                transcript.absorb_k(&lbl(p, &[b"seg"]), v);
                seg_vals.push(v);
                claims.push(Claim {
                    comp_id: sg.seg_id,
                    point,
                    value: v,
                });
            }
        }
    }
    drop(wfold);
    drop(eqi);
    let mut proof = SpartanProof {
        outer_msgs: msgs,
        outer_finals: finals,
        inner,
        v_w,
        seg_vals,
        xs_proof: None,
        xs_vals: None,
    };

    if let Some(cross) = cross {
        cross_prove(
            &mut proof,
            &mut claims,
            segments,
            cross,
            w,
            s,
            transcript,
            p,
            unchecked,
        );
    }
    (proof, claims)
}

struct XsSetup {
    lam: usize,
    tau: Vec<K>,
    gamma: K,
    claim: K,
    seg_in: Segment,
    seg_out: Segment,
}

fn xs_setup(
    cross: &CrossStep,
    segments: Option<&[Segment]>,
    s: usize,
    transcript: &mut Transcript,
    p: &[u8],
) -> Result<XsSetup, VerificationError> {
    let find = |id: i64| {
        segments
            .unwrap_or(&[])
            .iter()
            .find(|sg| sg.seg_id == id)
            .copied()
    };
    let (si, so) = match (find(cross.in_id), find(cross.out_id)) {
        (Some(si), Some(so))
            if si.kind != SegmentKind::Pad
                && so.kind != SegmentKind::Pad
                && si.log_cols == so.log_cols
                && cross.in_id != cross.out_id =>
        {
            (si, so)
        }
        _ => return Err(VerificationError::new("cross-step segments invalid")),
    };
    let lam = si.log_cols;
    if cross.init.len() != (1usize << lam) || cross.fin.len() != (1usize << lam) {
        return Err(VerificationError::new(
            "cross-step public state has wrong length",
        ));
    }
    let as_ks = |bits: &[bool]| -> Vec<K> { bits.iter().map(|&b| K::from_bit(b)).collect() };
    transcript.absorb_ks(&lbl(p, &[b"xs", b"init"]), &as_ks(&cross.init));
    transcript.absorb_ks(&lbl(p, &[b"xs", b"fin"]), &as_ks(&cross.fin));
    let tau = transcript.challenge_ks(&lbl(p, &[b"xs", b"tau"]), lam + s);
    let gamma = transcript.challenge_k(&lbl(p, &[b"xs", b"gamma"]));
    let claim = gamma * mle_eval_bits(&cross.init, &tau[..lam])
        + gamma * gamma * mle_eval_bits(&cross.fin, &tau[..lam]);
    Ok(XsSetup {
        lam,
        tau,
        gamma,
        claim,
        seg_in: si,
        seg_out: so,
    })
}

/// Evaluate instance `u`'s segment at `(off, n)` against `eq_col = eq_table(col_chals)`.
#[inline]
fn eval_segment_with_eq<R: BitRow>(row: &R, off: usize, n: usize, eq_col: &[K]) -> K {
    if let Some(words) = row.packed_words()
        && off.is_multiple_of(64)
        && n.is_multiple_of(64)
    {
        let wpr = n / 64;
        let base_wi = off / 64;
        let mut acc = K::ZERO;
        for w_idx in 0..wpr {
            let mut wv = words[base_wi + w_idx];
            let col_base = w_idx * 64;
            while wv != 0 {
                let b = wv.trailing_zeros() as usize;
                wv &= wv - 1;
                acc += eq_col[col_base + b];
            }
        }
        return acc;
    }
    let mut acc = K::ZERO;
    for (col, &ec) in eq_col.iter().enumerate().take(n) {
        if row.bit(off + col) {
            acc += ec;
        }
    }
    acc
}

#[allow(clippy::too_many_arguments)]
fn cross_prove<R: BitRow>(
    proof: &mut SpartanProof,
    claims: &mut Vec<Claim>,
    segments: Option<&[Segment]>,
    cross: &CrossStep,
    w: &[R],
    s: usize,
    transcript: &mut Transcript,
    p: &[u8],
    unchecked: bool,
) {
    let setup = xs_setup(cross, segments, s, transcript, p).expect("cross-step segments invalid");
    let (lam, gamma) = (setup.lam, setup.gamma);
    let mut claim = setup.claim;
    let (q, n) = (1usize << s, 1usize << lam);
    let (eqk, equ) = (eq_table(&setup.tau[..lam]), eq_table(&setup.tau[lam..]));
    let a_out_u: Vec<K> = (0..q)
        .map(|u| {
            (if u != q - 1 { equ[u] } else { K::ZERO })
                + (if u == q - 1 { gamma * gamma } else { K::ZERO })
        })
        .collect();
    let a_in_u: Vec<K> = (0..q)
        .map(|u| {
            (if u >= 1 { equ[u - 1] } else { K::ZERO }) + (if u == 0 { gamma } else { K::ZERO })
        })
        .collect();

    let (off_in, off_out) = (setup.seg_in.block << lam, setup.seg_out.block << lam);
    let combine = |v: &[K]| v[0] * (v[1] * v[2] + v[3] * v[4]);

    // By linearity over `K`, during the `lam` column rounds the instance
    // weights `a_out_u[u]` and `a_in_u[u]` are constant in the column
    // variables, so we fold the segments across instances once into a
    // `2^lam`-element column vector `f_col[k] = sum_u (a_out_u[u] S_out[u,k] + a_in_u[u] S_in[u,k])`.
    let chunk = q.div_ceil(4 * rayon::current_num_threads()).max(1);
    let mut f_col: Vec<K> = (0..q)
        .into_par_iter()
        .chunks(chunk)
        .map(|us| {
            let mut acc = vec![K::ZERO; n];
            for u in us {
                let ao = a_out_u[u];
                let ai = a_in_u[u];
                let row = &w[u];
                if let Some(words) = row.packed_words()
                    && off_out.is_multiple_of(64)
                    && off_in.is_multiple_of(64)
                    && n.is_multiple_of(64)
                {
                    let wpr = n / 64;
                    let wo_base = off_out / 64;
                    let wi_base = off_in / 64;
                    for w_idx in 0..wpr {
                        let mut wo = words[wo_base + w_idx];
                        while wo != 0 {
                            let b = wo.trailing_zeros() as usize;
                            wo &= wo - 1;
                            acc[w_idx * 64 + b] += ao;
                        }
                        let mut wi = words[wi_base + w_idx];
                        while wi != 0 {
                            let b = wi.trailing_zeros() as usize;
                            wi &= wi - 1;
                            acc[w_idx * 64 + b] += ai;
                        }
                    }
                } else {
                    for (col, slot) in acc.iter_mut().enumerate().take(n) {
                        if row.bit(off_out + col) {
                            *slot += ao;
                        }
                        if row.bit(off_in + col) {
                            *slot += ai;
                        }
                    }
                }
            }
            acc
        })
        .reduce(
            || vec![K::ZERO; n],
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(&b) {
                    *x += *y;
                }
                a
            },
        );

    if unchecked {
        claim = eqk
            .iter()
            .zip(&f_col)
            .fold(K::ZERO, |acc, (&ek, &fc)| acc + ek * fc);
    }
    let sc_label = lbl(p, &[b"xs", b"sc"]);
    sumcheck_init(transcript, &sc_label, claim, lam + s, 2);
    let (msg_label, chal_label) = (lbl(&sc_label, &[b"msg"]), lbl(&sc_label, &[b"chal"]));
    let (mut msgs, mut r_all): (Vec<Vec<K>>, Vec<K>) = (Vec::new(), Vec::new());
    let mut cur = claim;
    let mut eqk_bound = eqk;
    let mut col_chals: Vec<K> = Vec::with_capacity(lam);
    for _ in 0..lam {
        let half = eqk_bound.len() / 2;
        let mut ev = vec![K::ZERO; 3];
        for i in 0..half {
            let (e0, e1) = (eqk_bound[2 * i], eqk_bound[2 * i + 1]);
            let (f0, f1) = (f_col[2 * i], f_col[2 * i + 1]);
            let de = e0 + e1;
            let df = f0 + f1;
            ev[0] += e0 * f0;
            ev[1] += e1 * f1;
            ev[2] += (e0 + de.mul_x()) * (f0 + df.mul_x());
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
        r_all.push(chal);
        cur = interpolate_eval(&ev, chal);
        col_chals.push(chal);
        bind_low_in_place(&mut eqk_bound, chal);
        bind_low_in_place(&mut f_col, chal);
    }
    // Instance rounds over per-instance scalars.
    let eq_col = eq_table(&col_chals);
    let (out_s, in_s): (Vec<K>, Vec<K>) = if q >= 1 << 12 {
        (0..q)
            .into_par_iter()
            .map(|u| {
                (
                    eval_segment_with_eq(&w[u], off_out, n, &eq_col),
                    eval_segment_with_eq(&w[u], off_in, n, &eq_col),
                )
            })
            .unzip()
    } else {
        (0..q)
            .map(|u| {
                (
                    eval_segment_with_eq(&w[u], off_out, n, &eq_col),
                    eval_segment_with_eq(&w[u], off_in, n, &eq_col),
                )
            })
            .unzip()
    };
    let mut tables: Vec<Vec<K>> = vec![vec![eqk_bound[0]; q], a_out_u, out_s, a_in_u, in_s];
    for _ in 0..s {
        let ev = sumcheck_round_evals(&tables, &combine, 2);
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let msg = vec![ev[0], ev[2]];
        transcript.absorb_ks(&msg_label, &msg);
        let chal = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        r_all.push(chal);
        cur = interpolate_eval(&ev, chal);
        for tab in &mut tables {
            bind_low_in_place(tab, chal);
        }
    }
    let fin: Vec<K> = tables.iter().map(|tb| tb[0]).collect();
    let (sc, r) = (SumcheckProof { round_msgs: msgs }, r_all);
    let (v_out, v_in) = (fin[2], fin[4]);
    transcript.absorb_ks(&lbl(p, &[b"xs", b"final"]), &[v_in, v_out]);
    proof.xs_proof = Some(sc);
    proof.xs_vals = Some(vec![v_in, v_out]);
    claims.push(Claim {
        comp_id: cross.in_id,
        point: r.clone(),
        value: v_in,
    });
    claims.push(Claim {
        comp_id: cross.out_id,
        point: r,
        value: v_out,
    });
}

/// The Spartan verifier (spec 06 §6.3, 6.5, 6.6, 6.8). Returns the
/// output claims on success.
///
/// # Errors
/// Returns [`VerificationError`] mirroring Python's `verify` (see spec
/// 06 §6.8 for the ordered checks).
///
/// # Panics
/// Panics if `rels` is empty or the layout is invalid (Python raises
/// `IndexError` / `ValueError` — caller errors, not proof failures).
#[allow(clippy::too_many_arguments)]
#[allow(clippy::needless_range_loop)]
pub fn verify(
    rels: &[R1CS],
    s: usize,
    x: &[Vec<K>],
    proof: &SpartanProof,
    transcript: &mut Transcript,
    p: &[u8],
    names: Option<&[Vec<u8>]>,
    segments: Option<&[Segment]>,
    cross: Option<&CrossStep>,
) -> Result<Vec<Claim>, VerificationError> {
    let t = rels.len();
    let names = resolve_names(names, t);
    let (rho, nu) = {
        let first = rels.first().expect("no relations");
        (first.rho, first.nu)
    };
    let q = 1usize << s;
    if x.len() != q {
        return Err(VerificationError::new("wrong number of public inputs"));
    }
    let nx = x[0].len();
    if x.iter().any(|xi| xi.len() != nx) {
        return Err(VerificationError::new(
            "public inputs must have equal length",
        ));
    }
    if let Some(segs) = segments {
        check_layout(segs, nu);
    }
    if proof.outer_msgs.len() != t || proof.outer_finals.len() != t {
        return Err(VerificationError::new("malformed proof"));
    }
    if proof.outer_msgs.iter().any(|m| m.len() != rho + s) {
        return Err(VerificationError::new("wrong number of outer rounds"));
    }
    let tau = setup(transcript, p, t, rho, nu, s, nx, x, &names);

    let mut cur = vec![K::ZERO; t];
    let step = |cur: &mut [K], ti: usize, msg: &[K], r: K| -> Result<(), VerificationError> {
        if msg.len() != 3 {
            return Err(VerificationError::new("malformed outer message"));
        }
        let ys = [msg[0], cur[ti] + msg[0], msg[1], msg[2]];
        cur[ti] = interpolate_eval(&ys, r);
        Ok(())
    };

    let mut r_row: Vec<Vec<K>> = vec![Vec::new(); t];
    let mut r_inst: Vec<K> = Vec::new();
    for i in 0..rho {
        for ti in 0..t {
            let msg = &proof.outer_msgs[ti][i];
            transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"msg"]), msg);
            let r = transcript.challenge_k(&lbl(p, &[b"outer", &names[ti], b"row"]));
            step(&mut cur, ti, msg, r)?;
            r_row[ti].push(r);
        }
    }
    for i in 0..s {
        for ti in 0..t {
            transcript.absorb_ks(
                &lbl(p, &[b"outer", &names[ti], b"msg"]),
                &proof.outer_msgs[ti][rho + i],
            );
        }
        let r = transcript.challenge_k(&lbl(p, &[b"outer", b"inst"]));
        for ti in 0..t {
            step(&mut cur, ti, &proof.outer_msgs[ti][rho + i], r)?;
        }
        r_inst.push(r);
    }
    for ti in 0..t {
        let fv = &proof.outer_finals[ti];
        if fv.len() != 3 {
            return Err(VerificationError::new("malformed terminal values"));
        }
        let mut point = r_row[ti].clone();
        point.extend_from_slice(&r_inst);
        if cur[ti] != eq_eval(&tau[ti], &point) * (fv[0] * fv[1] + fv[2]) {
            return Err(VerificationError::new("outer sum-check final check failed"));
        }
        transcript.absorb_ks(&lbl(p, &[b"outer", &names[ti], b"final"]), fv);
    }
    let alpha = transcript.challenge_ks(&lbl(p, &[b"alpha"]), 3 * t);
    let mut v_star = K::ZERO;
    for ti in 0..t {
        for m in 0..3 {
            v_star += alpha[3 * ti + m] * proof.outer_finals[ti][m];
        }
    }
    let (r_y, e) = sumcheck_verify(
        v_star,
        nu,
        2,
        &proof.inner,
        transcript,
        &lbl(p, &[b"inner"]),
    )?;
    let mut mf = K::ZERO;
    for (ti, rel) in rels.iter().enumerate() {
        for (m, mat) in rel.mats().into_iter().enumerate() {
            mf += alpha[3 * ti + m] * mat.mle(&r_row[ti], &r_y);
        }
    }
    let r_col: Vec<K> = r_y[..nu - 1].to_vec();
    let top = r_y[nu - 1];
    let pub_eval = mle_eval(&fold_public(x, nu, &r_inst), &r_col);
    let v_z = (K::ONE + top) * proof.v_w + top * pub_eval;
    if e != mf * v_z {
        return Err(VerificationError::new("inner sum-check final check failed"));
    }
    transcript.absorb_k(&lbl(p, &[b"vw"]), proof.v_w);

    let mut claims: Vec<Claim> = Vec::new();
    match segments {
        None => {
            let mut point = r_col.clone();
            point.extend_from_slice(&r_inst);
            claims.push(Claim {
                comp_id: -1,
                point,
                value: proof.v_w,
            });
        }
        Some(segs) => {
            let real: Vec<&Segment> = segs
                .iter()
                .filter(|sg| sg.kind != SegmentKind::Pad)
                .collect();
            if proof.seg_vals.len() != real.len() {
                return Err(VerificationError::new("wrong number of segment claims"));
            }
            let mut acc = K::ZERO;
            for (sg, &v) in real.iter().zip(&proof.seg_vals) {
                transcript.absorb_k(&lbl(p, &[b"seg"]), v);
                let qi = &r_col[sg.log_cols..];
                acc += eq_eval(qi, &bits_of(sg.block, nu - 1 - sg.log_cols)) * v;
                let mut point: Vec<K> = r_col[..sg.log_cols].to_vec();
                point.extend_from_slice(&r_inst);
                claims.push(Claim {
                    comp_id: sg.seg_id,
                    point,
                    value: v,
                });
            }
            if acc != proof.v_w {
                return Err(VerificationError::new(
                    "segment claims inconsistent with v_W",
                ));
            }
        }
    }
    if let Some(cross) = cross {
        let xs = xs_setup(cross, segments, s, transcript, p)?;
        let (lam, gamma) = (xs.lam, xs.gamma);
        let (xs_proof, xs_vals) = match (&proof.xs_proof, &proof.xs_vals) {
            (Some(sc), Some(vals)) if vals.len() == 2 => (sc, vals),
            _ => return Err(VerificationError::new("missing cross-step proof")),
        };
        let (r, e) = sumcheck_verify(
            xs.claim,
            lam + s,
            2,
            xs_proof,
            transcript,
            &lbl(p, &[b"xs", b"sc"]),
        )?;
        let (v_in, v_out) = (xs_vals[0], xs_vals[1]);
        let (a_out, a_in) = xs_weights(&xs.tau[lam..], gamma, &r[lam..]);
        if e != eq_eval(&xs.tau[..lam], &r[..lam]) * (a_out * v_out + a_in * v_in) {
            return Err(VerificationError::new("cross-step final check failed"));
        }
        transcript.absorb_ks(&lbl(p, &[b"xs", b"final"]), &[v_in, v_out]);
        claims.push(Claim {
            comp_id: cross.in_id,
            point: r.clone(),
            value: v_in,
        });
        claims.push(Claim {
            comp_id: cross.out_id,
            point: r,
            value: v_out,
        });
    }
    Ok(claims)
}

#[cfg(test)]
mod tests {
    use super::*;
    use om_sumcheck::mle_eval_packed;

    /// A small xorshift generator (deterministic, test only).
    fn next(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    fn rand_k(state: &mut u64) -> K {
        K::from_u128(u128::from(next(state)) << 64 | u128::from(next(state)))
    }

    /// The factored, streaming helpers equal the dense definitions
    /// they replace, value for value.
    #[test]
    fn streaming_folds_match_dense() {
        let mut st = 0x9e37_79b9_7f4a_7c15u64;
        let (nu, s) = (7usize, 5usize);
        let half = 1usize << (nu - 1);
        let w: Vec<PackedBits> = (0..1usize << s)
            .map(|_| {
                let mut row = PackedBits::zero(half);
                for c in 0..half {
                    if next(&mut st) & 1 == 1 {
                        row.set(c);
                    }
                }
                row
            })
            .collect();
        let x: Vec<Vec<K>> = (0..1usize << s)
            .map(|_| (0..3).map(|_| rand_k(&mut st)).collect())
            .collect();
        let r_inst: Vec<K> = (0..s).map(|_| rand_k(&mut st)).collect();
        let r_col: Vec<K> = (0..nu - 1).map(|_| rand_k(&mut st)).collect();
        let eqi = eq_table(&r_inst);

        let mut dense = vec![K::ZERO; half];
        for (u, wu) in w.iter().enumerate() {
            for (c, slot) in dense.iter_mut().enumerate() {
                if wu.bit(c) {
                    *slot += eqi[u];
                }
            }
        }
        assert_eq!(fold_witness(&w, &eqi, half), dense);
        assert_eq!(
            fold_public_sparse(&x, nu, &eqi),
            fold_public(&x, nu, &r_inst)
        );

        let segs = [
            Segment {
                seg_id: 0,
                kind: SegmentKind::Direct,
                log_cols: 5,
                block: 0,
            },
            Segment {
                seg_id: 1,
                kind: SegmentKind::Pad,
                log_cols: 3,
                block: 4,
            },
            Segment {
                seg_id: 2,
                kind: SegmentKind::Virtual,
                log_cols: 3,
                block: 5,
            },
            Segment {
                seg_id: 3,
                kind: SegmentKind::Direct,
                log_cols: 0,
                block: 48,
            },
        ];
        check_layout(&segs, nu);
        let want: Vec<K> = segs
            .iter()
            .filter(|sg| sg.kind != SegmentKind::Pad)
            .map(|sg| {
                let mut point = r_col[..sg.log_cols].to_vec();
                point.extend_from_slice(&r_inst);
                mle_eval_packed(&segment_table_packed(&w, sg), &point)
            })
            .collect();
        assert_eq!(segment_values(&dense, &segs, &r_col), want);
    }
}
