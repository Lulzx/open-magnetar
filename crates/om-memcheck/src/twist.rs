//! BinaryTwist (spec 07 §7.5–7.7). Mirrors
//! `reference/openmagnetar/twist.py` byte for byte in its transcript
//! interaction.
//!
//! Address component tables: see [`crate::onehot`]. Inc table: index
//! `o + 2^ell * j`. Memory `M0` table: index `k + 2^a * o` (`k` low, C2).
//! Words are `u64`s (`2^ell <= 64` bits used, `ell <= 6` in v1).

use om_field::K;
use om_sumcheck::{
    SumcheckProof, VerificationError, bind_low, eq_eval, eq_table, interpolate_eval, mle_eval_bits,
    sumcheck_init, sumcheck_prove, sumcheck_round_evals, sumcheck_verify,
};
use om_transcript::Transcript;
use rayon::prelude::*;

use crate::onehot::PAR_THRESHOLD;
use crate::onehot::{
    EvalClaim, OneHotProof, VirtGroup, VirtProof, VirtTerm, bits_of, comp_tables, onehot_prove,
    onehot_verify, virt_prove, virt_verify,
};
use crate::sublabel;

/// `Σ_j f(j)` in `K` (XOR), parallel for large `n` — exact in any order.
fn xor_sum(n: usize, f: &(dyn Fn(usize) -> K + Sync)) -> K {
    if n >= PAR_THRESHOLD {
        (0..n)
            .into_par_iter()
            .map(f)
            .reduce(|| K::ZERO, |a, b| a + b)
    } else {
        (0..n).fold(K::ZERO, |acc, j| acc + f(j))
    }
}

/// Parameters of one BinaryTwist instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistParams {
    pub name: String,
    /// Memory has `2^a` cells.
    pub a: usize,
    /// Number of address components, `d | a`.
    pub d: usize,
    /// Reads per cycle (then one write).
    pub p: usize,
    /// `T = 2^n` cycles.
    pub n: usize,
    /// Words have `2^ell` bits (default 6 in Python).
    pub ell: usize,
}

impl TwistParams {
    /// Parameters with the Python default `ell = 6`.
    pub fn new(name: &str, a: usize, d: usize, p: usize, n: usize) -> Self {
        TwistParams {
            name: name.to_string(),
            a,
            d,
            p,
            n,
            ell: 6,
        }
    }
}

/// The input claims of one BinaryTwist instance, all at the common
/// value point `r_o` and cycle point `r_c`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistClaims {
    /// `K^ell`.
    pub r_o: Vec<K>,
    /// `K^n`.
    pub r_c: Vec<K>,
    /// `p` claimed values `rv_s~(r_o, r_c)`.
    pub rv: Vec<K>,
    /// `wv~(r_o, r_c)`.
    pub wv: K,
    /// `bits[x][t]`: address bit `t` of address `x` (`x < p` reads,
    /// `x = p` write) at `r_c`.
    pub bits: Vec<Vec<K>>,
}

/// Final-memory claim spec (spec 07 §7.6, C6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalMem {
    /// Output region has `2^m` words.
    pub m: usize,
    /// High `(a - m)` bits of the region's first word index.
    pub s_out: usize,
    /// `2^m` public output words.
    pub words: Vec<u64>,
}

/// The committed witness of one BinaryTwist instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistWitness {
    /// `ra[s]` = list of `d` component tables.
    pub ra: Vec<Vec<Vec<bool>>>,
    /// List of `d` component tables.
    pub wa: Vec<Vec<bool>>,
    /// 0/1 table, index `o + 2^ell * j`.
    pub inc: Vec<bool>,
}

/// Proof of one BinaryTwist instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistProof {
    pub rw: SumcheckProof,
    /// `[ra_0..ra_{p-1}, wa, V, I]`.
    pub rw_evals: Vec<K>,
    pub val: SumcheckProof,
    /// `[wa~(r_k, s), Inc~(r_o, s)]`.
    pub val_evals: Vec<K>,
    pub fin: Option<SumcheckProof>,
    pub fin_evals: Option<Vec<K>>,
    pub inc_extra: Option<K>,
    pub virt: Option<VirtProof>,
    pub onehot: OneHotProof,
}

/// Output of one BinaryTwist instance: the evaluation claims on
/// committed polynomials (spec 07 §7.5 step 9, in order) and the
/// optional Inc-at-a-random-point claim (§7.7, also the last entry of
/// `claims` when present).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistOutput {
    pub claims: Vec<EvalClaim>,
    pub inc_extra: Option<EvalClaim>,
}

/// The honest values computed by [`build_witness`] (Python's `info`
/// dict).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistInfo {
    /// `rv[s][j]`: word read by read `s` in cycle `j`.
    pub rv: Vec<Vec<u64>>,
    /// `wv[j]`: word written in cycle `j`.
    pub wv: Vec<u64>,
    /// `inc[j]`: XOR of old and new content of the written cell.
    pub inc: Vec<u64>,
    /// Memory state after the last cycle (Python key `"final"`).
    pub final_state: Vec<u64>,
    /// `reads[s][j]`: address of read `s` in cycle `j`.
    pub reads: Vec<Vec<usize>>,
    /// `writes[j]`: address written in cycle `j`.
    pub writes: Vec<usize>,
}

// ----------------------------------------------------------------- helpers

/// MLE of `LT(x, y) = [x < y]` (C2 order, `x_1` = LSB): `O(n)` field
/// operations. `LT~(x,y) = Σ_i (1 + x_i) y_i Π_{m > i} (1 + x_m + y_m)`.
///
/// # Panics
/// Panics if `x` and `y` have different lengths (indexing, as in
/// Python's `range(len(x))` against `y[i]`).
pub fn lt_eval(x: &[K], y: &[K]) -> K {
    let (mut acc, mut suffix) = (K::ZERO, K::ONE);
    for i in (0..x.len()).rev() {
        acc += (K::ONE + x[i]) * y[i] * suffix;
        suffix *= K::ONE + x[i] + y[i];
    }
    acc
}

/// The table `j ↦ LT~(bits(j), y)` of length `2^len(y)`.
pub fn lt_table(y: &[K]) -> Vec<K> {
    let n = y.len();
    let size = 1usize << n;
    if size >= PAR_THRESHOLD {
        (0..size)
            .into_par_iter()
            .map(|j| lt_eval(&bits_of(j as u64, n), y))
            .collect()
    } else {
        (0..size)
            .map(|j| lt_eval(&bits_of(j as u64, n), y))
            .collect()
    }
}

/// All component names in one-hot order: reads `0..p-1` each with
/// components `1..d`, then the write components `1..d`.
pub fn comp_names_tw(params: &TwistParams) -> Vec<String> {
    let mut nm = Vec::with_capacity((params.p + 1) * params.d);
    for s in 0..params.p {
        nm.extend((0..params.d).map(|i| format!("{}/ra{}/{}", params.name, s, i + 1)));
    }
    nm.extend((0..params.d).map(|i| format!("{}/wa/{}", params.name, i + 1)));
    nm
}

/// Bit table of a list of words, index `o + 2^ell * j` (bit `o` of
/// `words[j]`).
pub fn word_table(words: &[u64], ell: usize) -> Vec<bool> {
    let l = 1usize << ell;
    let total = words.len() * l;
    let at = |idx: usize| (words[idx / l] >> (idx % l)) & 1 == 1;
    if total >= PAR_THRESHOLD {
        (0..total).into_par_iter().map(at).collect()
    } else {
        (0..total).map(at).collect()
    }
}

/// From an access trace (`reads[s][j]`, `writes[j]`, `new_words[j]`)
/// build the witness and the honest values, replaying memory starting
/// from `m0` (one word per cell).
pub fn build_witness(
    params: &TwistParams,
    m0: &[u64],
    reads: &[Vec<usize>],
    writes: &[usize],
    new_words: &[u64],
) -> (TwistWitness, TwistInfo) {
    let (a, d, p, n, ell) = (params.a, params.d, params.p, params.n, params.ell);
    let t = 1usize << n;
    let mut state = m0.to_vec();
    let mut rv = vec![vec![0u64; t]; p];
    let (mut wv, mut inc) = (vec![0u64; t], vec![0u64; t]);
    for j in 0..t {
        for s in 0..p {
            rv[s][j] = state[reads[s][j]];
        }
        let old = state[writes[j]];
        inc[j] = old ^ new_words[j];
        state[writes[j]] = new_words[j];
        wv[j] = new_words[j];
    }
    let wit = TwistWitness {
        ra: (0..p).map(|s| comp_tables(&reads[s], a, d)).collect(),
        wa: comp_tables(writes, a, d),
        inc: word_table(&inc, ell),
    };
    let info = TwistInfo {
        rv,
        wv,
        inc,
        final_state: state,
        reads: reads.to_vec(),
        writes: writes.to_vec(),
    };
    (wit, info)
}

/// The honest input claims at `(r_o, r_c)` for the values in `info`.
pub fn honest_claims(params: &TwistParams, info: &TwistInfo, r_o: &[K], r_c: &[K]) -> TwistClaims {
    let (a, p, ell) = (params.a, params.p, params.ell);
    let mut pt = r_o.to_vec();
    pt.extend_from_slice(r_c);
    let rv: Vec<K> = (0..p)
        .map(|s| mle_eval_bits(&word_table(&info.rv[s], ell), &pt))
        .collect();
    let wv = mle_eval_bits(&word_table(&info.wv, ell), &pt);
    let mut addrs: Vec<&Vec<usize>> = info.reads.iter().collect();
    addrs.push(&info.writes);
    let bits: Vec<Vec<K>> = (0..=p)
        .map(|x| {
            (0..a)
                .map(|t| {
                    let col: Vec<bool> = addrs[x].iter().map(|&ad| (ad >> t) & 1 == 1).collect();
                    mle_eval_bits(&col, r_c)
                })
                .collect()
        })
        .collect();
    TwistClaims {
        r_o: r_o.to_vec(),
        r_c: r_c.to_vec(),
        rv,
        wv,
        bits,
    }
}

/// The `M_0` bit table, index `k + 2^a * o` (bit `o` of `m0[k]`).
pub fn m0_table(m0: &[u64], a: usize, ell: usize) -> Vec<bool> {
    let rows = m0.len().min(1usize << a);
    if rows == 0 {
        return Vec::new();
    }
    let total = rows << ell;
    let at = |idx: usize| (m0[idx % rows] >> (idx / rows)) & 1 == 1;
    if total >= PAR_THRESHOLD {
        (0..total).into_par_iter().map(at).collect()
    } else {
        (0..total).map(at).collect()
    }
}

/// The output-region bit table, index `k_low + 2^m * o` (bit `o` of
/// `words[k_low]`), where `2^m = words.len()`.
pub fn out_table(words: &[u64], ell: usize) -> Vec<bool> {
    if words.is_empty() {
        return Vec::new();
    }
    let total = words.len() << ell;
    let at = |idx: usize| (words[idx % words.len()] >> (idx / words.len())) & 1 == 1;
    if total >= PAR_THRESHOLD {
        (0..total).into_par_iter().map(at).collect()
    } else {
        (0..total).map(at).collect()
    }
}

fn absorb(tr: &mut Transcript, label: &[u8], c: &TwistClaims) {
    tr.absorb_ks(&sublabel(label, b"/point_o"), &c.r_o);
    tr.absorb_ks(&sublabel(label, b"/point_c"), &c.r_c);
    tr.absorb_ks(&sublabel(label, b"/rv"), &c.rv);
    tr.absorb_k(&sublabel(label, b"/wv"), c.wv);
    let flat: Vec<K> = c.bits.iter().flatten().copied().collect();
    tr.absorb_ks(&sublabel(label, b"/bits"), &flat);
}

fn coeffs(tr: &mut Transcript, label: &[u8], p: usize, a: usize) -> (Vec<K>, Vec<Vec<K>>, Vec<K>) {
    let (mut alpha0, mut alphas) = (Vec::with_capacity(p + 1), Vec::with_capacity(p + 1));
    for _ in 0..=p {
        alpha0.push(tr.challenge_nonzero_k(&sublabel(label, b"/alpha0")));
        alphas.push(tr.challenge_ks(&sublabel(label, b"/alpha"), a));
    }
    let beta = tr.challenge_ks(&sublabel(label, b"/beta"), p + 1);
    (alpha0, alphas, beta)
}

/// `Φ(k) = alpha0 + Σ_t alphas[t] k_t` as a table over Boolean `k`.
fn phi_k(alpha0: K, alphas: &[K], a: usize) -> Vec<K> {
    let nk = 1usize << a;
    let at = |k: usize| {
        let mut v = alpha0;
        for (t, &al) in alphas.iter().enumerate().take(a) {
            if (k >> t) & 1 == 1 {
                v += al;
            }
        }
        v
    };
    if nk >= PAR_THRESHOLD {
        (0..nk).into_par_iter().map(at).collect()
    } else {
        (0..nk).map(at).collect()
    }
}

/// Table layout: `[eq, V, I, ra_0..ra_p, phi_0..phi_p]`.
fn rw_combine(p: usize, beta: &[K], v: &[K]) -> K {
    let (eq, big_v, big_i) = (v[0], v[1], v[2]);
    let ra = &v[3..4 + p];
    let phi = &v[4 + p..];
    let mut acc = K::ZERO;
    for x in 0..=p {
        acc += beta[x] * ra[x] * (big_v + phi[x]);
    }
    acc += beta[p] * ra[p] * big_i;
    eq * acc
}

/// `g(j) = eq(r_k, write_addr(j))`: the write one-hot table contracted
/// over the address variables (equal to summing `eq(r_k, k)` against the
/// full table, which is a delta at the write address).
fn wa_rows(writes_addr: &[usize], r_k: &[K]) -> Vec<K> {
    let e = eq_table(r_k);
    writes_addr.iter().map(|&k| e[k]).collect()
}

fn s_out_bits(final_mem: &FinalMem, a: usize) -> Vec<K> {
    bits_of(final_mem.s_out as u64, a - final_mem.m)
}

#[allow(clippy::too_many_arguments)]
fn groups(
    params: &TwistParams,
    has_final: bool,
    r_k: &[K],
    r_j: &[K],
    rw_ev: &[K],
    s_v: &[K],
    val_ev: &[K],
    r_kf: Option<&[K]>,
    s_f: Option<&[K]>,
    fin_ev: Option<&[K]>,
) -> Vec<VirtGroup> {
    let (p, d) = (params.p, params.d);
    let nm = comp_names_tw(params);
    let mut groups = Vec::new();
    for s in 0..p {
        groups.push(VirtGroup {
            names: nm[s * d..(s + 1) * d].to_vec(),
            r_k: r_k.to_vec(),
            terms: vec![VirtTerm {
                cyc: r_j.to_vec(),
                value: rw_ev[s],
            }],
        });
    }
    groups.push(VirtGroup {
        names: nm[p * d..].to_vec(),
        r_k: r_k.to_vec(),
        terms: vec![
            VirtTerm {
                cyc: r_j.to_vec(),
                value: rw_ev[p],
            },
            VirtTerm {
                cyc: s_v.to_vec(),
                value: val_ev[0],
            },
        ],
    });
    if has_final {
        groups.push(VirtGroup {
            names: nm[p * d..].to_vec(),
            r_k: r_kf.expect("final group needs r_kf").to_vec(),
            terms: vec![VirtTerm {
                cyc: s_f.expect("final group needs s_f").to_vec(),
                value: fin_ev.expect("final group needs fin_evals")[0],
            }],
        });
    }
    groups
}

#[allow(clippy::too_many_arguments)]
fn inc_claims(
    params: &TwistParams,
    claims: &TwistClaims,
    r_j: &[K],
    rw_ev: &[K],
    s_v: &[K],
    val_ev: &[K],
    r_of: Option<&[K]>,
    s_f: Option<&[K]>,
    fin_ev: Option<&[K]>,
) -> Vec<EvalClaim> {
    let nm = format!("{}/inc", params.name);
    let pt = |pre: &[K], post: &[K]| {
        let mut v = pre.to_vec();
        v.extend_from_slice(post);
        v
    };
    let mut out = vec![
        EvalClaim {
            poly: nm.clone(),
            point: pt(&claims.r_o, r_j),
            value: *rw_ev.last().expect("rw_evals nonempty"),
        },
        EvalClaim {
            poly: nm.clone(),
            point: pt(&claims.r_o, s_v),
            value: val_ev[1],
        },
    ];
    if let Some(fin_ev) = fin_ev {
        out.push(EvalClaim {
            poly: nm,
            point: pt(
                r_of.expect("final inc claim needs r_of"),
                s_f.expect("final inc claim needs s_f"),
            ),
            value: fin_ev[1],
        });
    }
    out
}

// -----------------------------------------------------------------
// Sparse rw prover (spec 07 §7.10, informative). Same transcript and
// proof bytes as the dense definition in §7.5; only the prover's
// internal representation differs.
//
// The dense prover materialises tables of size `T * 2^a`. Here the
// first `n` sum-check rounds (cycle variables) work on one sparse
// group per remaining cycle suffix. A group stores, per access `x`,
// the sparse support of the bound one-hot table `ra_x` (at most one
// address per original cycle in the group), plus the scalars
// `A = sum_k ra_x(k) V(k)`, `B = sum_k ra_x(k) Phi_x(k)` and
// `S = sum_k ra_x(k)`, where `V` is the bound value table. Binding two
// sibling groups needs the cross term
// `sum_k ra_L(k) V_R(k) + ra_R(k) V_L(k)`, where `V` of a group at an
// arbitrary address is recomputed from that address's write list:
// the state of a cell is constant between its writes, and the
// eq-weight of a constant segment is a range sum over the bound
// cycle bits. After the cycle rounds, one group remains and the last
// `a` rounds run densely on tables of size `2^a` only.

/// Per-access sparse state of one cycle group.
#[derive(Clone)]
struct RwX {
    /// `(address, bound ra value)` pairs, sorted by address.
    entries: Vec<(usize, K)>,
    /// `sum_k ra(k) * V(k)` for the bound tables of this group.
    aval: K,
    /// `sum_k ra(k) * Phi(k)`.
    bval: K,
    /// `sum_k ra(k)`.
    sval: K,
}

/// One remaining cycle suffix in the sparse phase.
#[derive(Clone)]
struct RwGroup {
    /// Bound `eq(r_c, .)` value of this group.
    eq: K,
    /// Bound `Inc~(r_o, .)` value of this group.
    inc: K,
    /// Per access `0..=p` (`p` is the write).
    per_x: Vec<RwX>,
}

/// Everything the sparse phase needs to evaluate `V(k, j)` on demand.
struct SparseMem<'a> {
    m0: &'a [u64],
    /// Per address: `(cycle, inc)` writes in cycle order.
    writes: Vec<Vec<(usize, u64)>>,
    /// Per address: prefix XORs of the write increments.
    prefix: Vec<Vec<u64>>,
    /// `eq_table(r_o)`: bit weights for `Val~`.
    eo: &'a [K],
}

impl SparseMem<'_> {
    fn val_at(&self, state: u64) -> K {
        let mut acc = K::ZERO;
        for (o, &e) in self.eo.iter().enumerate() {
            if (state >> o) & 1 == 1 {
                acc += e;
            }
        }
        acc
    }

    /// Memory word of cell `k` just before cycle `j`.
    fn state_at(&self, k: usize, j: usize) -> u64 {
        let ws = &self.writes[k];
        let cnt = ws.partition_point(|w| w.0 < j);
        self.m0[k] ^ self.prefix[k][cnt]
    }

    /// `V~(k)` of the group covering cycles `[base, base + 2^r)`, with
    /// the cycle bits bound to `rhos` (low bit first).
    fn v_group(&self, k: usize, base: usize, r: usize, rhos: &[K]) -> K {
        let end = base + (1usize << r);
        let ws = &self.writes[k];
        let mut state = self.state_at(k, base);
        let mut acc = K::ZERO;
        let mut cur = base;
        for &(w, inc) in ws.iter().filter(|w| w.0 >= base && w.0 < end) {
            // State is constant on cycles `cur..=w` (the write at `w`
            // lands after cycle `w` reads the old value).
            acc += eq_range_sum(rhos, cur - base, w - base) * self.val_at(state);
            state ^= inc;
            cur = w + 1;
        }
        if cur < end {
            acc += eq_range_sum(rhos, cur - base, end - 1 - base) * self.val_at(state);
        }
        acc
    }
}

/// `sum_{offset in [lo, hi]} prod_b (bit_b(offset) ? rho_b : 1 + rho_b)`.
fn eq_range_sum(rhos: &[K], lo: usize, hi: usize) -> K {
    if lo > hi {
        return K::ZERO;
    }
    if rhos.is_empty() {
        return K::ONE;
    }
    let h = rhos.len() - 1;
    let mid = 1usize << h;
    let (f0, f1) = (K::ONE + rhos[h], rhos[h]);
    if hi < mid {
        f0 * eq_range_sum(&rhos[..h], lo, hi)
    } else if lo >= mid {
        f1 * eq_range_sum(&rhos[..h], lo - mid, hi - mid)
    } else {
        f0 * eq_range_sum(&rhos[..h], lo, mid - 1) + f1 * eq_range_sum(&rhos[..h], 0, hi - mid)
    }
}

/// Address accessed in every cycle, reconstructed from the one-hot
/// component tables of access `x` (chunk `i` holds bits `i*ac..`).
fn addrs_of(comps: &[Vec<bool>], a: usize, d: usize, t: usize) -> Vec<usize> {
    let (ac, nu) = (a / d, 1usize << (a / d));
    let mut addr = vec![0usize; t];
    for (i, comp) in comps.iter().enumerate() {
        for (idx, &bit) in comp.iter().enumerate() {
            if bit {
                addr[idx / nu] |= (idx % nu) << (i * ac);
            }
        }
    }
    addr
}

/// Merge two sorted `(address, value)` lists with coefficients.
fn merge_entries(l: &[(usize, K)], r: &[(usize, K)], c0: K, c1: K) -> Vec<(usize, K)> {
    let mut out = Vec::with_capacity(l.len() + r.len());
    let (mut i, mut j) = (0, 0);
    while i < l.len() && j < r.len() {
        match l[i].0.cmp(&r[j].0) {
            core::cmp::Ordering::Less => {
                out.push((l[i].0, c0 * l[i].1));
                i += 1;
            }
            core::cmp::Ordering::Greater => {
                out.push((r[j].0, c1 * r[j].1));
                j += 1;
            }
            core::cmp::Ordering::Equal => {
                out.push((l[i].0, c0 * l[i].1 + c1 * r[j].1));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend(l[i..].iter().map(|&(k, v)| (k, c0 * v)));
    out.extend(r[j..].iter().map(|&(k, v)| (k, c1 * v)));
    out
}

/// The sparse rw sum-check of `twist_prove`. Returns the same triple
/// as `sumcheck_prove` on the dense tables of §7.5: proof, all
/// challenges (`r_j` then `r_k`), and the table MLEs at the point.
#[allow(clippy::too_many_arguments)]
fn rw_sumcheck_sparse(
    params: &TwistParams,
    m0: &[u64],
    wit: &TwistWitness,
    claims: &TwistClaims,
    alpha0: &[K],
    alphas: &[Vec<K>],
    beta: &[K],
    transcript: &mut Transcript,
    label: &[u8],
) -> (SumcheckProof, Vec<K>, Vec<K>) {
    let (a, d, p, n, ell) = (params.a, params.d, params.p, params.n, params.ell);
    let (nk, t, l) = (1usize << a, 1usize << n, 1usize << ell);
    assert_eq!(m0.len(), nk, "twist_prove: m0 must have 2^a words");

    // Address of every access in every cycle.
    let mut addrs: Vec<Vec<usize>> = wit
        .ra
        .iter()
        .map(|comps| addrs_of(comps, a, d, t))
        .collect();
    let writes_addr = addrs_of(&wit.wa, a, d, t);
    addrs.push(writes_addr.clone());

    // Inc as integers and as `Inc~(r_o, j)` field values.
    let eo = eq_table(&claims.r_o);
    let mut inc_int = vec![0u64; t];
    let mut inc_val = vec![K::ZERO; t];
    for j in 0..t {
        let (mut iv, mut acc) = (0u64, K::ZERO);
        for (o, &e) in eo.iter().enumerate() {
            if wit.inc[o + l * j] {
                iv |= 1 << o;
                acc += e;
            }
        }
        inc_int[j] = iv;
        inc_val[j] = acc;
    }

    // Sparse memory: write list and prefix XORs per address.
    let mut writes: Vec<Vec<(usize, u64)>> = vec![Vec::new(); nk];
    for (j, &k) in writes_addr.iter().enumerate() {
        writes[k].push((j, inc_int[j]));
    }
    let prefix: Vec<Vec<u64>> = writes
        .iter()
        .map(|ws| {
            let mut pref = Vec::with_capacity(ws.len() + 1);
            pref.push(0u64);
            for &(_, inc) in ws {
                let last = *pref.last().unwrap();
                pref.push(last ^ inc);
            }
            pref
        })
        .collect();
    let mem = SparseMem {
        m0,
        writes,
        prefix,
        eo: &eo,
    };

    let phi_at = |x: usize, k: usize| -> K {
        let mut v = alpha0[x];
        for (bit, &al) in alphas[x].iter().enumerate() {
            if (k >> bit) & 1 == 1 {
                v += al;
            }
        }
        v
    };

    // Initial groups: one per cycle, replaying memory for `A`.
    let eqc = eq_table(&claims.r_c);
    let mut state = m0.to_vec();
    let mut groups: Vec<RwGroup> = Vec::with_capacity(t);
    for j in 0..t {
        let per_x = (0..=p)
            .map(|x| RwX {
                entries: vec![(addrs[x][j], K::ONE)],
                aval: mem.val_at(state[addrs[x][j]]),
                bval: phi_at(x, addrs[x][j]),
                sval: K::ONE,
            })
            .collect();
        groups.push(RwGroup {
            eq: eqc[j],
            inc: inc_val[j],
            per_x,
        });
        state[writes_addr[j]] ^= inc_int[j];
    }

    let total_of = |groups: &[RwGroup]| -> K {
        let mut acc = K::ZERO;
        for g in groups {
            let mut inner = beta[p] * g.inc * g.per_x[p].sval;
            for (x, &bx) in beta.iter().enumerate().take(p + 1) {
                inner += bx * (g.per_x[x].aval + g.per_x[x].bval);
            }
            acc += g.eq * inner;
        }
        acc
    };
    let claim = total_of(&groups);
    sumcheck_init(transcript, label, claim, n + a, 3);
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let (mut msgs, mut rs): (Vec<Vec<K>>, Vec<K>) = (Vec::new(), Vec::new());
    let mut cur = claim;
    let mut rhos: Vec<K> = Vec::with_capacity(n);

    // Cycle rounds over the sparse groups.
    for round in 0..n {
        let r = round;
        let half = groups.len() / 2;
        // Cross terms per pair and access, computed once per round.
        let mut crosses: Vec<Vec<K>> = Vec::with_capacity(half);
        for pair in 0..half {
            let (gl, gr) = (&groups[2 * pair], &groups[2 * pair + 1]);
            let (base_l, base_r) = (2 * pair * (1usize << r), (2 * pair + 1) * (1usize << r));
            let mut cx = Vec::with_capacity(p + 1);
            for x in 0..=p {
                let mut cross = K::ZERO;
                for &(k, ra) in &gl.per_x[x].entries {
                    cross += ra * mem.v_group(k, base_r, r, &rhos);
                }
                for &(k, ra) in &gr.per_x[x].entries {
                    cross += ra * mem.v_group(k, base_l, r, &rhos);
                }
                cx.push(cross);
            }
            crosses.push(cx);
        }
        let mut ev = vec![K::ZERO; 4];
        for (tt, slot) in ev.iter_mut().enumerate() {
            let tv = K::t(tt as u128);
            let (c0, c1) = (K::ONE + tv, tv);
            for pair in 0..half {
                let (gl, gr) = (&groups[2 * pair], &groups[2 * pair + 1]);
                let eq_t = c0 * gl.eq + c1 * gr.eq;
                let mut inner = K::ZERO;
                for x in 0..=p {
                    let a_t = c0 * c0 * gl.per_x[x].aval
                        + c1 * c1 * gr.per_x[x].aval
                        + c0 * c1 * crosses[pair][x];
                    let b_t = c0 * gl.per_x[x].bval + c1 * gr.per_x[x].bval;
                    inner += beta[x] * (a_t + b_t);
                }
                let s_p = c0 * gl.per_x[p].sval + c1 * gr.per_x[p].sval;
                let i_t = c0 * gl.inc + c1 * gr.inc;
                inner += beta[p] * i_t * s_p;
                *slot += eq_t * inner;
            }
        }
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = vec![ev[0]];
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let chal = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(chal);
        cur = interpolate_eval(&ev, chal);
        rhos.push(chal);
        // Bind: merge sibling groups.
        let (c0, c1) = (K::ONE + chal, chal);
        let mut next: Vec<RwGroup> = Vec::with_capacity(half);
        for pair in 0..half {
            let (gl, gr) = (&groups[2 * pair], &groups[2 * pair + 1]);
            let per_x = (0..=p)
                .map(|x| RwX {
                    entries: merge_entries(&gl.per_x[x].entries, &gr.per_x[x].entries, c0, c1),
                    aval: c0 * c0 * gl.per_x[x].aval
                        + c1 * c1 * gr.per_x[x].aval
                        + c0 * c1 * crosses[pair][x],
                    bval: c0 * gl.per_x[x].bval + c1 * gr.per_x[x].bval,
                    sval: c0 * gl.per_x[x].sval + c1 * gr.per_x[x].sval,
                })
                .collect();
            next.push(RwGroup {
                eq: c0 * gl.eq + c1 * gr.eq,
                inc: c0 * gl.inc + c1 * gr.inc,
                per_x,
            });
        }
        groups = next;
    }

    // Address rounds: dense tables of size `2^a` only.
    let group = &groups[0];
    let eqw = eq_table(&rhos);
    let mut hist: Vec<Vec<K>> = vec![vec![K::ZERO; nk]; p + 1];
    for j in 0..t {
        for x in 0..=p {
            hist[x][addrs[x][j]] += eqw[j];
        }
    }
    let vtab: Vec<K> = (0..nk).map(|k| mem.v_group(k, 0, n, &rhos)).collect();
    let mut tables: Vec<Vec<K>> = vec![vec![group.eq; nk], vtab, vec![group.inc; nk]];
    tables.extend(hist);
    for x in 0..=p {
        tables.push(phi_k(alpha0[x], &alphas[x], a));
    }
    let combine = {
        let beta = beta.to_vec();
        move |v: &[K]| rw_combine(p, &beta, v)
    };
    for _ in 0..a {
        let ev = sumcheck_round_evals(&tables, &combine, 3);
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = vec![ev[0]];
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let chal = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(chal);
        cur = interpolate_eval(&ev, chal);
        tables = tables.iter().map(|tb| bind_low(tb, chal)).collect();
    }
    let mles: Vec<K> = tables.iter().map(|tb| tb[0]).collect();
    (SumcheckProof { round_msgs: msgs }, rs, mles)
}

/// Prove one BinaryTwist instance (spec 07 §7.5), with the optional
/// final-memory claim (§7.6) and Inc-at-a-random-point output (§7.7).
#[allow(clippy::too_many_arguments)]
pub fn twist_prove(
    params: &TwistParams,
    m0: &[u64],
    wit: &TwistWitness,
    claims: &TwistClaims,
    transcript: &mut Transcript,
    label: &[u8],
    final_mem: Option<&FinalMem>,
    inc_extra_flag: bool,
) -> (TwistProof, TwistOutput) {
    let (a, d, p, n, ell) = (params.a, params.d, params.p, params.n, params.ell);
    let (nk, t, l) = (1usize << a, 1usize << n, 1usize << ell);
    absorb(transcript, label, claims);
    let (alpha0, alphas, beta) = coeffs(transcript, label, p, a);

    // `I(j) = Inc~(r_o, j)`, and the write address of every cycle; both
    // are also needed by the Val and final-memory steps below.
    let eo = eq_table(&claims.r_o);
    let big_i: Vec<K> = (0..t)
        .map(|j| {
            let mut acc = K::ZERO;
            for (o, &e) in eo.iter().enumerate() {
                if wit.inc[o + l * j] {
                    acc += e;
                }
            }
            acc
        })
        .collect();
    let writes_addr = addrs_of(&wit.wa, a, d, t);
    assert_eq!(m0.len(), nk, "twist_prove: m0 must have 2^a words");
    // The rw sum-check runs sparsely (§7.10): no `T * 2^a` tables.
    let (rw, r, mles) = rw_sumcheck_sparse(
        params,
        m0,
        wit,
        claims,
        &alpha0,
        &alphas,
        &beta,
        transcript,
        &sublabel(label, b"/rw"),
    );
    let (r_j, r_k) = (r[..n].to_vec(), r[n..].to_vec());
    let mut rw_ev: Vec<K> = (0..=p).map(|x| mles[3 + x]).collect();
    rw_ev.push(mles[1]);
    rw_ev.push(mles[2]);
    transcript.absorb_ks(&sublabel(label, b"/rw/evals"), &rw_ev);

    // Val evaluation
    let wa_r = wa_rows(&writes_addr, &r_k);
    let lt = lt_table(&r_j);
    let claim = xor_sum(t, &|j| lt[j] * wa_r[j] * big_i[j]);
    let mul3 = |v: &[K]| v[0] * v[1] * v[2];
    let (val, s_v, mles) = sumcheck_prove(
        claim,
        vec![lt, wa_r, big_i.clone()],
        &mul3,
        3,
        transcript,
        &sublabel(label, b"/val"),
    );
    let val_ev = vec![mles[1], mles[2]];
    transcript.absorb_ks(&sublabel(label, b"/val/evals"), &val_ev);

    // Final memory
    let (mut fin, mut fin_ev) = (None, None);
    let (mut r_kf, mut s_f, mut r_of) = (None, None, None);
    if let Some(final_mem) = final_mem {
        let r_low = transcript.challenge_ks(&sublabel(label, b"/fin/r_low"), final_mem.m);
        let rof = transcript.challenge_ks(&sublabel(label, b"/fin/r_o"), ell);
        let mut rkf = r_low;
        rkf.extend(s_out_bits(final_mem, a));
        let eof = eq_table(&rof);
        let wa_f = wa_rows(&writes_addr, &rkf);
        let if_at = |j: usize| {
            let mut acc = K::ZERO;
            for (o, &e) in eof.iter().enumerate() {
                if wit.inc[o + l * j] {
                    acc += e;
                }
            }
            acc
        };
        let i_f: Vec<K> = if t * l >= PAR_THRESHOLD {
            (0..t).into_par_iter().map(if_at).collect()
        } else {
            (0..t).map(if_at).collect()
        };
        let claim = xor_sum(t, &|j| wa_f[j] * i_f[j]);
        let mul2 = |v: &[K]| v[0] * v[1];
        let (fin_sc, sf, mles) = sumcheck_prove(
            claim,
            vec![wa_f, i_f],
            &mul2,
            2,
            transcript,
            &sublabel(label, b"/fin"),
        );
        let fev = vec![mles[0], mles[1]];
        transcript.absorb_ks(&sublabel(label, b"/fin/evals"), &fev);
        fin = Some(fin_sc);
        fin_ev = Some(fev);
        r_kf = Some(rkf);
        s_f = Some(sf);
        r_of = Some(rof);
    }

    let (mut extra, mut extra_claim) = (None, None);
    if inc_extra_flag {
        let xo = transcript.challenge_ks(&sublabel(label, b"/incx/o"), ell);
        let xc = transcript.challenge_ks(&sublabel(label, b"/incx/c"), n);
        let mut pt = xo;
        pt.extend_from_slice(&xc);
        let value = mle_eval_bits(&wit.inc, &pt);
        transcript.absorb_k(&sublabel(label, b"/incx/val"), value);
        extra = Some(value);
        extra_claim = Some(EvalClaim {
            poly: format!("{}/inc", params.name),
            point: pt,
            value,
        });
    }

    let grps = groups(
        params,
        final_mem.is_some(),
        &r_k,
        &r_j,
        &rw_ev,
        &s_v,
        &val_ev,
        r_kf.as_deref(),
        s_f.as_deref(),
        fin_ev.as_deref(),
    );
    let mut comps_per_group: Vec<Vec<Vec<bool>>> = wit.ra.clone();
    comps_per_group.push(wit.wa.clone());
    if final_mem.is_some() {
        comps_per_group.push(wit.wa.clone());
    }
    let (vproof, mut out_claims) = virt_prove(
        &grps,
        &comps_per_group,
        a,
        d,
        n,
        transcript,
        &sublabel(label, b"/virt"),
    );
    let mut all_comps: Vec<Vec<bool>> = wit.ra.iter().flatten().cloned().collect();
    all_comps.extend(wit.wa.iter().cloned());
    let (oproof, oclaims) = onehot_prove(
        &all_comps,
        &comp_names_tw(params),
        a / d,
        n,
        transcript,
        &sublabel(label, b"/onehot"),
    );
    out_claims.extend(oclaims);
    out_claims.extend(inc_claims(
        params,
        claims,
        &r_j,
        &rw_ev,
        &s_v,
        &val_ev,
        r_of.as_deref(),
        s_f.as_deref(),
        fin_ev.as_deref(),
    ));
    if let Some(ec) = &extra_claim {
        out_claims.push(ec.clone());
    }
    let out = TwistOutput {
        claims: out_claims,
        inc_extra: extra_claim,
    };
    (
        TwistProof {
            rw,
            rw_evals: rw_ev,
            val,
            val_evals: val_ev,
            fin,
            fin_evals: fin_ev,
            inc_extra: extra,
            virt: vproof,
            onehot: oproof,
        },
        out,
    )
}

/// Verify one BinaryTwist instance, returning its output claims.
/// `m0_eval(point)` must return `M0~(point)` for
/// `point = r_k ‖ r_o` (`a + ell` coordinates).
///
/// # Errors
/// Returns [`VerificationError`] on malformed claims or proof, a proof
/// whose shape does not match the instance, or any failing check.
#[allow(clippy::too_many_arguments)]
pub fn twist_verify(
    params: &TwistParams,
    m0_eval: &dyn Fn(&[K]) -> K,
    claims: &TwistClaims,
    proof: &TwistProof,
    transcript: &mut Transcript,
    label: &[u8],
    final_mem: Option<&FinalMem>,
    inc_extra_flag: bool,
) -> Result<TwistOutput, VerificationError> {
    let (a, d, p, n, ell) = (params.a, params.d, params.p, params.n, params.ell);
    if claims.rv.len() != p
        || claims.bits.len() != p + 1
        || claims.r_o.len() != ell
        || claims.r_c.len() != n
        || claims.bits.iter().any(|b| b.len() != a)
    {
        return Err(VerificationError::new("twist: malformed claims"));
    }
    if proof.rw_evals.len() != p + 3 || proof.val_evals.len() != 2 {
        return Err(VerificationError::new("twist: malformed proof"));
    }
    if final_mem.is_none() != proof.fin.is_none() || inc_extra_flag != proof.inc_extra.is_some() {
        return Err(VerificationError::new(
            "twist: proof shape does not match instance",
        ));
    }
    absorb(transcript, label, claims);
    let (alpha0, alphas, beta) = coeffs(transcript, label, p, a);
    let mut claim = K::ZERO;
    for x in 0..=p {
        let v = if x < p { claims.rv[x] } else { claims.wv };
        let mut t_acc = v + alpha0[x];
        for (&al, &f) in alphas[x].iter().zip(&claims.bits[x]) {
            t_acc += al * f;
        }
        claim += beta[x] * t_acc;
    }
    let (r, expected) = sumcheck_verify(
        claim,
        n + a,
        3,
        &proof.rw,
        transcript,
        &sublabel(label, b"/rw"),
    )?;
    let (r_j, r_k) = (r[..n].to_vec(), r[n..].to_vec());
    let ev = &proof.rw_evals;
    transcript.absorb_ks(&sublabel(label, b"/rw/evals"), ev);
    let (big_v, big_i) = (ev[p + 1], ev[p + 2]);
    let mut acc = K::ZERO;
    for x in 0..=p {
        let mut phi = alpha0[x];
        for (&al, &rk) in alphas[x].iter().zip(&r_k) {
            phi += al * rk;
        }
        acc += beta[x] * ev[x] * (big_v + phi);
    }
    acc += beta[p] * ev[p] * big_i;
    if eq_eval(&claims.r_c, &r_j) * acc != expected {
        return Err(VerificationError::new("twist: read/write check failed"));
    }

    let mut m0_pt = r_k.clone();
    m0_pt.extend_from_slice(&claims.r_o);
    let claim = big_v + m0_eval(&m0_pt);
    let (s_v, expected) = sumcheck_verify(
        claim,
        n,
        3,
        &proof.val,
        transcript,
        &sublabel(label, b"/val"),
    )?;
    transcript.absorb_ks(&sublabel(label, b"/val/evals"), &proof.val_evals);
    if lt_eval(&s_v, &r_j) * proof.val_evals[0] * proof.val_evals[1] != expected {
        return Err(VerificationError::new("twist: val check failed"));
    }

    let (mut r_kf, mut s_f, mut r_of, mut fin_ev) = (None, None, None, None);
    if let Some(final_mem) = final_mem {
        if final_mem.words.len() != 1usize << final_mem.m
            || final_mem.s_out >= 1usize << (a - final_mem.m)
        {
            return Err(VerificationError::new("twist: bad final-memory spec"));
        }
        let r_low = transcript.challenge_ks(&sublabel(label, b"/fin/r_low"), final_mem.m);
        let rof = transcript.challenge_ks(&sublabel(label, b"/fin/r_o"), ell);
        let mut rkf = r_low.clone();
        rkf.extend(s_out_bits(final_mem, a));
        let mut out_pt = r_low;
        out_pt.extend_from_slice(&rof);
        let mut m0_pt = rkf.clone();
        m0_pt.extend_from_slice(&rof);
        let claim = mle_eval_bits(&out_table(&final_mem.words, ell), &out_pt) + m0_eval(&m0_pt);
        let fin_sc = proof
            .fin
            .as_ref()
            .ok_or_else(|| VerificationError::new("twist: proof shape does not match instance"))?;
        let (sf, expected) =
            sumcheck_verify(claim, n, 2, fin_sc, transcript, &sublabel(label, b"/fin"))?;
        let fev = proof
            .fin_evals
            .as_ref()
            .ok_or_else(|| VerificationError::new("twist: malformed final evals"))?;
        if fev.len() != 2 {
            return Err(VerificationError::new("twist: malformed final evals"));
        }
        transcript.absorb_ks(&sublabel(label, b"/fin/evals"), fev);
        if fev[0] * fev[1] != expected {
            return Err(VerificationError::new("twist: final-memory check failed"));
        }
        fin_ev = Some(fev.clone());
        r_kf = Some(rkf);
        s_f = Some(sf);
        r_of = Some(rof);
    }

    let mut extra_claim = None;
    if inc_extra_flag {
        let xo = transcript.challenge_ks(&sublabel(label, b"/incx/o"), ell);
        let xc = transcript.challenge_ks(&sublabel(label, b"/incx/c"), n);
        let value = proof
            .inc_extra
            .ok_or_else(|| VerificationError::new("twist: proof shape does not match instance"))?;
        transcript.absorb_k(&sublabel(label, b"/incx/val"), value);
        let mut pt = xo;
        pt.extend_from_slice(&xc);
        extra_claim = Some(EvalClaim {
            poly: format!("{}/inc", params.name),
            point: pt,
            value,
        });
    }

    let grps = groups(
        params,
        final_mem.is_some(),
        &r_k,
        &r_j,
        ev,
        &s_v,
        &proof.val_evals,
        r_kf.as_deref(),
        s_f.as_deref(),
        fin_ev.as_deref(),
    );
    let mut out_claims = virt_verify(
        &grps,
        a,
        d,
        n,
        proof.virt.as_ref(),
        transcript,
        &sublabel(label, b"/virt"),
    )?;
    let oclaims = onehot_verify(
        &comp_names_tw(params),
        a / d,
        n,
        &proof.onehot,
        transcript,
        &sublabel(label, b"/onehot"),
    )?;
    out_claims.extend(oclaims);
    out_claims.extend(inc_claims(
        params,
        claims,
        &r_j,
        ev,
        &s_v,
        &proof.val_evals,
        r_of.as_deref(),
        s_f.as_deref(),
        fin_ev.as_deref(),
    ));
    if let Some(ec) = &extra_claim {
        out_claims.push(ec.clone());
    }
    Ok(TwistOutput {
        claims: out_claims,
        inc_extra: extra_claim,
    })
}
