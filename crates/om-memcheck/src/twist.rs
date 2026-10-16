//! BinaryTwist (spec 07 §7.5–7.7). Mirrors
//! `reference/openmagnetar/twist.py` byte for byte in its transcript
//! interaction.
//!
//! Address component tables: see [`crate::onehot`]. Inc table: index
//! `o + 2^ell * j`. Memory `M0` table: index `k + 2^a * o` (`k` low, C2).
//! Words are `u64`s (`2^ell <= 64` bits used, `ell <= 6` in v1).

use om_field::K;
use om_sumcheck::{
    PackedBits, SumcheckProof, VerificationError, bind_low_in_place, eq_eval, eq_table,
    interpolate_eval, mle_eval_bits, sumcheck_init, sumcheck_round_evals, sumcheck_verify,
};
use om_transcript::Transcript;
use rayon::prelude::*;

use crate::lazy::{SplitEq, SplitLt, WordEval, eq_weighted_sum, sumcheck_prove_rows};
use crate::onehot::PAR_THRESHOLD;
use crate::onehot::{
    AddrComps, EvalClaim, OneHotProof, VirtGroup, VirtProof, VirtTerm, bits_of, onehot_prove,
    onehot_verify, virt_prove, virt_verify,
};
use crate::sublabel;

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

/// The committed witness of one BinaryTwist instance, in the compact
/// form of spec 07 §7.10: the address components as one address per
/// cycle (or arbitrary bit tables, for cheating-prover tests), and the
/// `Inc` table as one word per cycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwistWitness {
    /// `ra[s]`: the `d` components of read `s`.
    pub ra: Vec<AddrComps>,
    /// The `d` components of the write address.
    pub wa: AddrComps,
    /// `inc[j]`: the increment word of cycle `j`; the committed `Inc`
    /// table is bit `o` of `inc[j]` at index `o + 2^ell * j`, `o <
    /// 2^ell` (higher bits are ignored).
    pub inc: Vec<u64>,
}

impl TwistWitness {
    /// The `Inc` bit table, index `o + 2^ell * j` (as [`word_table`]).
    pub fn inc_table(&self, ell: usize) -> Vec<bool> {
        word_table(&self.inc, ell)
    }

    /// The `Inc` bit table, packed.
    pub fn inc_packed(&self, ell: usize) -> PackedBits {
        if ell == 6 {
            return PackedBits::from_words(self.inc.clone(), self.inc.len() * 64);
        }
        let l = 1usize << ell;
        let mut out = PackedBits::zero(self.inc.len() * l);
        for (j, &w) in self.inc.iter().enumerate() {
            let mut w = if l >= 64 { w } else { w & ((1u64 << l) - 1) };
            while w != 0 {
                let o = w.trailing_zeros() as usize;
                out.set(o + l * j);
                w &= w - 1;
            }
        }
        out
    }
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
    let (p, n) = (params.p, params.n);
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
    let to32 = |v: &[usize]| -> Vec<u32> {
        v.iter()
            .map(|&x| u32::try_from(x).expect("address fits in u32"))
            .collect()
    };
    let wit = build_witness_lean(
        params,
        m0,
        reads.iter().map(|r| to32(r)).collect(),
        to32(writes),
        new_words,
    );
    debug_assert_eq!(wit.inc, inc);
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

/// The witness alone (no honest-value side tables): what the prover
/// commits to. `reads[s][j]` and `writes[j]` are word addresses below
/// `2^a`, moved into the witness.
///
/// # Panics
/// Panics if a sequence does not have `2^n` entries or an address is
/// out of range.
pub fn build_witness_lean(
    params: &TwistParams,
    m0: &[u64],
    reads: Vec<Vec<u32>>,
    writes: Vec<u32>,
    new_words: &[u64],
) -> TwistWitness {
    let (a, d, p, n) = (params.a, params.d, params.p, params.n);
    let t = 1usize << n;
    assert!(
        reads.len() == p && reads.iter().all(|r| r.len() == t),
        "build_witness: need p read sequences of 2^n addresses"
    );
    assert!(
        writes.len() == t && new_words.len() == t,
        "build_witness: need 2^n writes"
    );
    let mut state = m0.to_vec();
    let mut inc = vec![0u64; t];
    for j in 0..t {
        let k = writes[j] as usize;
        inc[j] = state[k] ^ new_words[j];
        state[k] = new_words[j];
    }
    TwistWitness {
        ra: reads
            .into_iter()
            .map(|r| AddrComps::from_addrs(r, a, d))
            .collect(),
        wa: AddrComps::from_addrs(writes, a, d),
        inc,
    }
}

/// `MLE(word_table(words, ell))(r_o ‖ r_c)` (`ell = len(r_o)`), in
/// `O(T)` without the `2^ell · T` table.
pub fn word_mle_eval(words: &[u64], r_o: &[K], r_c: &[K]) -> K {
    assert_eq!(words.len(), 1usize << r_c.len(), "word_mle_eval: length");
    let we = WordEval::new(r_o);
    eq_weighted_sum(r_c, &|j| we.eval(words[j]))
}

/// The address-bit claims `bits[x][t] = f_t~(r_c)` of every access
/// (`x < p` reads, `x = p` the write), as in [`honest_claims`].
pub fn addr_bit_claims(params: &TwistParams, wit: &TwistWitness, r_c: &[K]) -> Vec<Vec<K>> {
    wit.ra
        .iter()
        .chain(std::iter::once(&wit.wa))
        .map(|c| c.bit_evals(params.a, r_c))
        .collect()
}

/// The honest input claims at `(r_o, r_c)` for the values in `info`.
pub fn honest_claims(params: &TwistParams, info: &TwistInfo, r_o: &[K], r_c: &[K]) -> TwistClaims {
    let (a, p) = (params.a, params.p);
    let rv: Vec<K> = (0..p)
        .map(|s| word_mle_eval(&info.rv[s], r_o, r_c))
        .collect();
    let wv = word_mle_eval(&info.wv, r_o, r_c);
    let mut addrs: Vec<&Vec<usize>> = info.reads.iter().collect();
    addrs.push(&info.writes);
    let bits: Vec<Vec<K>> = (0..=p)
        .map(|x| crate::lazy::addr_bit_evals(a, r_c, &|j| addrs[x][j]))
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
// address per original cycle in the group) and the scalar
// `A = sum_k ra_x(k) V(k)`, where `V` is the bound value table;
// `sum_k ra_x(k) Phi_x(k)` and `sum_k ra_x(k)` are recomputed from the
// support. Binding two sibling groups needs the cross term
// `sum_k ra_L(k) V_R(k) + ra_R(k) V_L(k)`, where `V` of a group at an
// arbitrary address is recomputed from that address's write list:
// the state of a cell is constant between its writes, and the
// eq-weight of a constant segment is a difference of prefix sums of
// the bound cycle eq table. Round 1 reads the per-cycle data directly
// (no groups are built); later rounds keep the groups in flat CSR
// arrays. After the cycle rounds, one group remains and the last `a`
// rounds run densely on tables of size `2^a` only.

/// Per-address write lists (CSR, group order) with the eq-weighted average
/// value `v_avg` of the cell on that group and the value `v_after` of the
/// cell right after that group's last cycle. Bound in-place after each cycle
/// sum-check round so `v_group` is always a single binary search with zero
/// inner loops over writes.
struct WriteLog {
    off: Vec<usize>,
    len: Vec<usize>,
    grp: Vec<u32>,
    v_avg: Vec<K>,
    v_after: Vec<K>,
    /// `Val~` of `M_0` per cell.
    m0val: Vec<K>,
}

impl WriteLog {
    /// Builds the initial (cycle-level) write log along with `(aval0, inc_val)`:
    /// `aval0[j * np + x]` is the `Val~` of cell `addrs[x][j]` just before
    /// cycle `j`, and `inc_val[j] = we.eval(inc[j])`.
    fn new(m0: &[u64], addrs: &[&[u32]], inc: &[u64], we: &WordEval) -> (Self, Vec<K>, Vec<K>) {
        let nk = m0.len();
        let np = addrs.len();
        let writes = addrs[np - 1];
        let mut off = vec![0usize; nk + 1];
        for &k in writes {
            off[k as usize + 1] += 1;
        }
        let len: Vec<usize> = (0..nk).map(|k| off[k + 1]).collect();
        for k in 0..nk {
            off[k + 1] += off[k];
        }
        let eval = |w: &u64| we.eval(*w);
        let (inc_val, m0val): (Vec<K>, Vec<K>) = if writes.len() + nk >= PAR_THRESHOLD {
            (
                inc.par_iter().map(eval).collect(),
                m0.par_iter().map(eval).collect(),
            )
        } else {
            (
                inc.iter().map(eval).collect(),
                m0.iter().map(eval).collect(),
            )
        };
        let mut pos = off[..nk].to_vec();
        let mut grp = vec![0u32; writes.len()];
        let mut v_avg = vec![K::ZERO; writes.len()];
        let mut v_after = vec![K::ZERO; writes.len()];
        let mut aval0 = vec![K::ZERO; writes.len() * np];
        let mut cur = m0val.clone();
        for (j, &k_u32) in writes.iter().enumerate() {
            let base_a = j * np;
            for (x, ad) in addrs.iter().enumerate() {
                aval0[base_a + x] = cur[ad[j] as usize];
            }
            let k = k_u32 as usize;
            let before = cur[k];
            let after = before + inc_val[j];
            cur[k] = after;
            let idx = pos[k];
            grp[idx] = u32::try_from(j).expect("T fits in u32");
            v_avg[idx] = before;
            v_after[idx] = after;
            pos[k] = idx + 1;
        }
        (
            WriteLog {
                off,
                len,
                grp,
                v_avg,
                v_after,
                m0val,
            },
            aval0,
            inc_val,
        )
    }

    /// `V~(k)` of group `g` at the current cycle-binding round.
    #[inline]
    fn v_group(&self, k: usize, g: usize) -> K {
        let lo = self.off[k];
        let hi = lo + self.len[k];
        let g32 = g as u32;
        let idx = self.grp[lo..hi].partition_point(|&c| c < g32);
        if lo + idx < hi && self.grp[lo + idx] == g32 {
            self.v_avg[lo + idx]
        } else if idx == 0 {
            self.m0val[k]
        } else {
            self.v_after[lo + idx - 1]
        }
    }

    /// Bind the low cycle variable of all write segments with challenge `chal`.
    fn bind(&mut self, chal: K) {
        let (c0, c1) = (K::ONE + chal, chal);
        for k in 0..self.m0val.len() {
            let lo = self.off[k];
            let n_k = self.len[k];
            if n_k == 0 {
                continue;
            }
            let mut prev_after = self.m0val[k];
            let mut r_idx = 0usize;
            let mut w_idx = 0usize;
            while r_idx < n_k {
                let g0 = self.grp[lo + r_idx];
                let m = g0 >> 1;
                let gl = m << 1;
                let gr = gl | 1;
                let (avg_l, after_l) = if g0 == gl {
                    let a = self.v_avg[lo + r_idx];
                    let f = self.v_after[lo + r_idx];
                    r_idx += 1;
                    (a, f)
                } else {
                    (prev_after, prev_after)
                };
                let (avg_r, after_r) = if r_idx < n_k && self.grp[lo + r_idx] == gr {
                    let a = self.v_avg[lo + r_idx];
                    let f = self.v_after[lo + r_idx];
                    r_idx += 1;
                    (a, f)
                } else {
                    (after_l, after_l)
                };
                self.grp[lo + w_idx] = m;
                self.v_avg[lo + w_idx] = c0 * avg_l + c1 * avg_r;
                self.v_after[lo + w_idx] = after_r;
                prev_after = after_r;
                w_idx += 1;
            }
            self.len[k] = w_idx;
        }
    }
}

/// The remaining cycle groups of the rw sum-check.
enum RwView<'a> {
    /// Before the first binding: one group per cycle, read from the
    /// per-cycle data.
    Cycles {
        addrs: &'a [&'a [u32]],
        inc_val: Vec<K>,
        aval0: Vec<K>,
        eqc: SplitEq,
    },
    /// Bound groups: per group `eq`, `inc`, `A_x` (`aval[g * (p+1) +
    /// x]`), and per access a CSR list of `(address, ra)` sorted by
    /// address.
    Csr {
        eq: Vec<K>,
        inc: Vec<K>,
        aval: Vec<K>,
        off: Vec<Vec<usize>>,
        keys: Vec<Vec<u32>>,
        vals: Vec<Vec<K>>,
    },
}

impl RwView<'_> {
    fn len(&self) -> usize {
        match self {
            RwView::Cycles { inc_val, .. } => inc_val.len(),
            RwView::Csr { eq, .. } => eq.len(),
        }
    }

    #[inline]
    fn eq(&self, g: usize) -> K {
        match self {
            RwView::Cycles { eqc, .. } => eqc.at(g),
            RwView::Csr { eq, .. } => eq[g],
        }
    }

    #[inline]
    fn inc(&self, g: usize) -> K {
        match self {
            RwView::Cycles { inc_val, .. } => inc_val[g],
            RwView::Csr { inc, .. } => inc[g],
        }
    }

    #[inline]
    fn aval(&self, g: usize, x: usize, np: usize) -> K {
        match self {
            RwView::Cycles { aval0, .. } => aval0[g * np + x],
            RwView::Csr { aval, .. } => aval[g * np + x],
        }
    }

    /// Support of group `g`, access `x`: keys and values (`None`: all
    /// values are one).
    #[inline]
    fn entries(&self, g: usize, x: usize) -> (&[u32], Option<&[K]>) {
        match self {
            RwView::Cycles { addrs, .. } => (&addrs[x][g..g + 1], None),
            RwView::Csr {
                off, keys, vals, ..
            } => {
                let (lo, hi) = (off[x][g], off[x][g + 1]);
                (&keys[x][lo..hi], Some(&vals[x][lo..hi]))
            }
        }
    }
}

#[inline]
fn entry_val(vals: Option<&[K]>, i: usize) -> K {
    vals.map_or(K::ONE, |v| v[i])
}

/// Number of distinct keys in two sorted lists.
fn merged_len(l: &[u32], r: &[u32]) -> usize {
    let (mut i, mut j, mut c) = (0, 0, 0);
    while i < l.len() && j < r.len() {
        match l[i].cmp(&r[j]) {
            core::cmp::Ordering::Less => i += 1,
            core::cmp::Ordering::Greater => j += 1,
            core::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
        }
        c += 1;
    }
    c + (l.len() - i) + (r.len() - j)
}

/// Merge two sorted `(address, value)` lists with coefficients into
/// `keys`/`vals` (exactly `merged_len` slots).
#[allow(clippy::too_many_arguments)]
fn merge_into(
    lk: &[u32],
    lv: Option<&[K]>,
    rk: &[u32],
    rv: Option<&[K]>,
    c0: K,
    c1: K,
    keys: &mut [u32],
    vals: &mut [K],
) {
    let (mut i, mut j, mut o) = (0, 0, 0);
    while i < lk.len() || j < rk.len() {
        let take_l = j >= rk.len() || (i < lk.len() && lk[i] <= rk[j]);
        let take_r = i >= lk.len() || (j < rk.len() && rk[j] <= lk[i]);
        let mut v = K::ZERO;
        let k = if take_l { lk[i] } else { rk[j] };
        if take_l {
            v += c0 * entry_val(lv, i);
            i += 1;
        }
        if take_r {
            v += c1 * entry_val(rv, j);
            j += 1;
        }
        keys[o] = k;
        vals[o] = v;
        o += 1;
    }
    debug_assert_eq!(o, keys.len());
}

/// Pairs per parallel work item when building the next CSR view.
const BIND_CHUNK: usize = 1 << 10;

/// Bind the sibling groups of `view` at `chal` into the next CSR view.
fn rw_bind(view: &RwView<'_>, crosses: &[K], np: usize, chal: K) -> RwView<'static> {
    let half = view.len() / 2;
    let (c0, c1) = (K::ONE + chal, chal);
    let par = view.len() >= PAR_THRESHOLD;
    let mut eq = vec![K::ZERO; half];
    let mut inc = vec![K::ZERO; half];
    let mut aval = vec![K::ZERO; half * np];
    let scal = |(m, (e, (ic, av))): (usize, (&mut K, (&mut K, &mut [K])))| {
        *e = c0 * view.eq(2 * m) + c1 * view.eq(2 * m + 1);
        *ic = c0 * view.inc(2 * m) + c1 * view.inc(2 * m + 1);
        for (x, slot) in av.iter_mut().enumerate() {
            *slot = c0 * c0 * view.aval(2 * m, x, np)
                + c1 * c1 * view.aval(2 * m + 1, x, np)
                + c0 * c1 * crosses[m * np + x];
        }
    };
    if par {
        eq.par_iter_mut()
            .zip(inc.par_iter_mut().zip(aval.par_chunks_mut(np)))
            .enumerate()
            .for_each(scal);
    } else {
        eq.iter_mut()
            .zip(inc.iter_mut().zip(aval.chunks_mut(np)))
            .enumerate()
            .for_each(scal);
    }
    let (mut offs, mut keys_all, mut vals_all) = (Vec::new(), Vec::new(), Vec::new());
    for x in 0..np {
        // Exact sizes first, then fill disjoint chunks in parallel.
        let mut off = vec![0usize; half + 1];
        let count = |(m, c): (usize, &mut usize)| {
            *c = merged_len(view.entries(2 * m, x).0, view.entries(2 * m + 1, x).0);
        };
        if par {
            off[1..].par_iter_mut().enumerate().for_each(count);
        } else {
            off[1..].iter_mut().enumerate().for_each(count);
        }
        for m in 0..half {
            off[m + 1] += off[m];
        }
        let total = off[half];
        let mut keys = vec![0u32; total];
        let mut vals = vec![K::ZERO; total];
        let mut pieces: Vec<(usize, &mut [u32], &mut [K])> = Vec::new();
        let (mut krest, mut vrest) = (&mut keys[..], &mut vals[..]);
        let mut m0 = 0;
        while m0 < half {
            let m1 = (m0 + BIND_CHUNK).min(half);
            let sz = off[m1] - off[m0];
            let (kh, kt) = krest.split_at_mut(sz);
            let (vh, vt) = vrest.split_at_mut(sz);
            pieces.push((m0, kh, vh));
            krest = kt;
            vrest = vt;
            m0 = m1;
        }
        let fill = |(m0, ks, vs): (usize, &mut [u32], &mut [K])| {
            let m1 = (m0 + BIND_CHUNK).min(half);
            let base = off[m0];
            for m in m0..m1 {
                let (lk, lv) = view.entries(2 * m, x);
                let (rk, rv) = view.entries(2 * m + 1, x);
                let (a, b) = (off[m] - base, off[m + 1] - base);
                merge_into(lk, lv, rk, rv, c0, c1, &mut ks[a..b], &mut vs[a..b]);
            }
        };
        if par {
            pieces.into_par_iter().for_each(fill);
        } else {
            pieces.into_iter().for_each(fill);
        }
        offs.push(off);
        keys_all.push(keys);
        vals_all.push(vals);
    }
    RwView::Csr {
        eq,
        inc,
        aval,
        off: offs,
        keys: keys_all,
        vals: vals_all,
    }
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
    let (a, p, n) = (params.a, params.p, params.n);
    let (nk, _t, np) = (1usize << a, 1usize << n, params.p + 1);
    assert_eq!(m0.len(), nk, "twist_prove: m0 must have 2^a words");

    // Address of every access in every cycle (`p` is the write).
    let addr_cows: Vec<std::borrow::Cow<'_, [u32]>> = wit
        .ra
        .iter()
        .chain(std::iter::once(&wit.wa))
        .map(|c| c.addrs())
        .collect();
    let addrs: Vec<&[u32]> = addr_cows.iter().map(|c| &c[..]).collect();
    let ie = WordEval::new(&claims.r_o);
    let (mut log, aval0, inc_val) = WriteLog::new(m0, &addrs, &wit.inc, &ie);
    let phis: Vec<Vec<K>> = (0..np).map(|x| phi_k(alpha0[x], &alphas[x], a)).collect();

    let mut view = RwView::Cycles {
        addrs: &addrs,
        inc_val,
        aval0,
        eqc: SplitEq::new(&claims.r_c),
    };
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let (mut msgs, mut rs): (Vec<Vec<K>>, Vec<K>) = (Vec::new(), Vec::new());
    let mut cur = K::ZERO;
    let ts: Vec<K> = (0..4).map(|k| K::t(k as u128)).collect();

    if n == 0 {
        // No cycle rounds: the claim is the single group's total.
        let mut inner = beta[p] * view.inc(0);
        for x in 0..np {
            let (ks, vs) = view.entries(0, x);
            let mut b = K::ZERO;
            for (i, &k) in ks.iter().enumerate() {
                b += entry_val(vs, i) * phis[x][k as usize];
            }
            inner += beta[x] * (view.aval(0, x, np) + b);
        }
        cur = view.eq(0) * inner;
        sumcheck_init(transcript, label, cur, a, 3);
    }

    // Cycle rounds over the sparse groups.
    for r in 0..n {
        let half = view.len() / 2;
        let par = view.len() >= PAR_THRESHOLD;
        let mut crosses = vec![K::ZERO; half * np];
        // Per pair: cross terms (stored for the binding) and the
        // contribution to the round evaluations.
        let pair = |mut ev: [K; 4], (m, cx): (usize, &mut [K])| -> [K; 4] {
            let (gl, gr) = (2 * m, 2 * m + 1);
            let (eql, eqr) = (view.eq(gl), view.eq(gr));
            let (il, ir) = (view.inc(gl), view.inc(gr));
            let (mut al_sum, mut ar_sum, mut ac_sum) = (K::ZERO, K::ZERO, K::ZERO);
            let (mut bl_sum, mut br_sum) = (K::ZERO, K::ZERO);
            let (mut sl, mut sr) = (K::ZERO, K::ZERO);
            if r == 0 {
                let w_l = addrs[p][gl];
                for x in 0..np {
                    let k_l = addrs[x][gl];
                    let k_r = addrs[x][gr];
                    let v_l = view.aval(gl, x, np);
                    let v_r = view.aval(gr, x, np);
                    let mut cross = v_l + v_r;
                    if k_l == w_l {
                        cross += il;
                    }
                    if k_r == w_l {
                        cross += il;
                    }
                    cx[x] = cross;
                    let bx = beta[x];
                    al_sum += bx * v_l;
                    ar_sum += bx * v_r;
                    ac_sum += bx * cross;
                    bl_sum += bx * phis[x][k_l as usize];
                    br_sum += bx * phis[x][k_r as usize];
                }
                sl = K::ONE;
                sr = K::ONE;
            } else {
                for x in 0..np {
                    let (lk, lv) = view.entries(gl, x);
                    let (rk, rv) = view.entries(gr, x);
                    let mut cross = K::ZERO;
                    let (mut bl_x, mut br_x) = (K::ZERO, K::ZERO);
                    for (i, &k) in lk.iter().enumerate() {
                        let v = entry_val(lv, i);
                        cross += v * log.v_group(k as usize, gr);
                        bl_x += v * phis[x][k as usize];
                        if x == p {
                            sl += v;
                        }
                    }
                    for (i, &k) in rk.iter().enumerate() {
                        let v = entry_val(rv, i);
                        cross += v * log.v_group(k as usize, gl);
                        br_x += v * phis[x][k as usize];
                        if x == p {
                            sr += v;
                        }
                    }
                    cx[x] = cross;
                    let bx = beta[x];
                    al_sum += bx * view.aval(gl, x, np);
                    ar_sum += bx * view.aval(gr, x, np);
                    ac_sum += bx * cross;
                    bl_sum += bx * bl_x;
                    br_sum += bx * br_x;
                }
            }
            let bp = beta[p];
            ev[0] += eql * (al_sum + bl_sum + bp * il * sl);
            ev[1] += eqr * (ar_sum + br_sum + bp * ir * sr);
            for (slot, &tv) in ev[2..].iter_mut().zip(&ts[2..]) {
                let (c0, c1) = (K::ONE + tv, tv);
                let eq_t = c0 * eql + c1 * eqr;
                let a_t = c0 * c0 * al_sum + c1 * c1 * ar_sum + c0 * c1 * ac_sum;
                let b_t = c0 * bl_sum + c1 * br_sum;
                let i_t = bp * (c0 * il + c1 * ir) * (c0 * sl + c1 * sr);
                *slot += eq_t * (a_t + b_t + i_t);
            }
            ev
        };
        let add4 = |mut a: [K; 4], b: [K; 4]| {
            for (x, y) in a.iter_mut().zip(b) {
                *x += y;
            }
            a
        };
        let ev: [K; 4] = if par {
            crosses
                .par_chunks_mut(np)
                .enumerate()
                .fold(|| [K::ZERO; 4], pair)
                .reduce(|| [K::ZERO; 4], add4)
        } else {
            crosses.chunks_mut(np).enumerate().fold([K::ZERO; 4], pair)
        };
        if r == 0 {
            cur = ev[0] + ev[1];
            sumcheck_init(transcript, label, cur, n + a, 3);
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
        let next = rw_bind(&view, &crosses, np, chal);
        drop(crosses);
        view = next;
        log.bind(chal);
    }

    // Address rounds: dense tables of size `2^a` only.
    let mut hist: Vec<Vec<K>> = vec![vec![K::ZERO; nk]; np];
    for (x, h) in hist.iter_mut().enumerate() {
        let (ks, vs) = view.entries(0, x);
        for (i, &k) in ks.iter().enumerate() {
            h[k as usize] += entry_val(vs, i);
        }
    }
    let (eq0, inc0) = (view.eq(0), view.inc(0));
    drop(view);
    let vat = |k: usize| log.v_group(k, 0);
    let vtab: Vec<K> = if nk >= PAR_THRESHOLD {
        (0..nk).into_par_iter().map(vat).collect()
    } else {
        (0..nk).map(vat).collect()
    };
    drop(log);
    let mut tables: Vec<Vec<K>> = vec![vec![eq0; nk], vtab, vec![inc0; nk]];
    tables.extend(hist);
    tables.extend(phis);
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
        for tb in &mut tables {
            bind_low_in_place(tb, chal);
        }
    }
    let mles: Vec<K> = tables.iter().map(|tb| tb[0]).collect();
    (SumcheckProof { round_msgs: msgs }, rs, mles)
}

/// Prove one BinaryTwist instance (spec 07 §7.5), with the optional
/// final-memory claim (§7.6) and Inc-at-a-random-point output (§7.7).
///
/// Every sum-check runs on per-cycle data (addresses and `Inc` words)
/// without full-length tables (§7.10); the bytes are those of the
/// dense definition.
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
    let nk = 1usize << a;
    assert_eq!(wit.inc.len(), 1usize << n, "twist_prove: Inc length");
    absorb(transcript, label, claims);
    let (alpha0, alphas, beta) = coeffs(transcript, label, p, a);
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

    // Val evaluation: tables `LT~(j, r_j)`, `eq(r_k, wa(j))`,
    // `Inc~(r_o, j)`, evaluated per cycle.
    let writes_addr = wit.wa.addrs();
    let ie = WordEval::new(&claims.r_o);
    {
        let (lt, ek) = (SplitLt::new(&r_j), eq_table(&r_k));
        let row = |j: usize, out: &mut [K]| {
            out[0] = lt.at(j);
            out[1] = ek[writes_addr[j] as usize];
            out[2] = ie.eval(wit.inc[j]);
        };
        let mul3 = |v: &[K]| v[0] * v[1] * v[2];
        let (_, val, s_v, mles) =
            sumcheck_prove_rows(n, 3, &row, &mul3, 3, transcript, &sublabel(label, b"/val"));
        let val_ev = vec![mles[1], mles[2]];
        transcript.absorb_ks(&sublabel(label, b"/val/evals"), &val_ev);
        twist_prove_tail(
            params,
            wit,
            claims,
            transcript,
            label,
            final_mem,
            inc_extra_flag,
            &writes_addr,
            (rw, rw_ev, r_j, r_k),
            (val, val_ev, s_v),
            (d, ell),
        )
    }
}

/// The steps of [`twist_prove`] after the Val sum-check: final memory,
/// `Inc` at a random point, virtualization and the one-hot check.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn twist_prove_tail(
    params: &TwistParams,
    wit: &TwistWitness,
    claims: &TwistClaims,
    transcript: &mut Transcript,
    label: &[u8],
    final_mem: Option<&FinalMem>,
    inc_extra_flag: bool,
    writes_addr: &[u32],
    (rw, rw_ev, r_j, r_k): (SumcheckProof, Vec<K>, Vec<K>, Vec<K>),
    (val, val_ev, s_v): (SumcheckProof, Vec<K>, Vec<K>),
    (d, ell): (usize, usize),
) -> (TwistProof, TwistOutput) {
    let (a, n) = (params.a, params.n);
    // Final memory
    let (mut fin, mut fin_ev) = (None, None);
    let (mut r_kf, mut s_f, mut r_of) = (None, None, None);
    if let Some(final_mem) = final_mem {
        let r_low = transcript.challenge_ks(&sublabel(label, b"/fin/r_low"), final_mem.m);
        let rof = transcript.challenge_ks(&sublabel(label, b"/fin/r_o"), ell);
        let mut rkf = r_low;
        rkf.extend(s_out_bits(final_mem, a));
        let (ekf, ief) = (eq_table(&rkf), WordEval::new(&rof));
        let row = |j: usize, out: &mut [K]| {
            out[0] = ekf[writes_addr[j] as usize];
            out[1] = ief.eval(wit.inc[j]);
        };
        let mul2 = |v: &[K]| v[0] * v[1];
        let (_, fin_sc, sf, mles) =
            sumcheck_prove_rows(n, 2, &row, &mul2, 2, transcript, &sublabel(label, b"/fin"));
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
        let value = word_mle_eval(&wit.inc, &xo, &xc);
        let mut pt = xo;
        pt.extend_from_slice(&xc);
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
    let mut comps_per_group: Vec<&AddrComps> = wit.ra.iter().collect();
    comps_per_group.push(&wit.wa);
    if final_mem.is_some() {
        comps_per_group.push(&wit.wa);
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
    let mut all_comps: Vec<&AddrComps> = wit.ra.iter().collect();
    all_comps.push(&wit.wa);
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
