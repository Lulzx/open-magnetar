//! Memory-lean prover helpers (spec 07 §7.10, informative): a sum-check
//! whose tables are never materialised at full length, split `eq`
//! tables, and word evaluation by byte lookup. None of this changes a
//! transcript byte: every round message is the same field element the
//! dense prover computes (field arithmetic is exact, so the order of
//! the sums does not matter).

use om_field::K;
use om_sumcheck::{
    SumcheckProof, bind_low_in_place, eq_table, interpolate_eval, sumcheck_init,
    sumcheck_round_evals,
};
use om_transcript::Transcript;
use rayon::prelude::*;

use crate::onehot::PAR_THRESHOLD;
use crate::sublabel;

/// Rounds computed directly from the row function before the bound
/// tables (then `2^-DIRECT_ROUNDS` of full length) are materialised.
pub(crate) const DIRECT_ROUNDS: usize = 1;

/// `eq(r, j)` for all `j < 2^len(r)` from two tables of size about
/// `2^(len/2)`: one multiplication per lookup instead of a `2^len(r)`
/// table.
pub(crate) struct SplitEq {
    pub(crate) lo: Vec<K>,
    pub(crate) hi: Vec<K>,
    pub(crate) h: usize,
}

impl SplitEq {
    pub(crate) fn new(r: &[K]) -> Self {
        let h = r.len() / 2;
        SplitEq {
            lo: eq_table(&r[..h]),
            hi: eq_table(&r[h..]),
            h,
        }
    }

    #[inline]
    pub(crate) fn at(&self, j: usize) -> K {
        self.lo[j & ((1usize << self.h) - 1)] * self.hi[j >> self.h]
    }
}

/// `LT~(bits(j), y)` for all `j < 2^len(y)` from split tables, using
/// `LT(x, y) = LT(x_hi, y_hi) + eq(x_hi, y_hi) · LT(x_lo, y_lo)`.
pub(crate) struct SplitLt {
    lt_lo: Vec<K>,
    lt_hi: Vec<K>,
    eq_hi: Vec<K>,
    h: usize,
}

impl SplitLt {
    pub(crate) fn new(y: &[K]) -> Self {
        let h = y.len() / 2;
        SplitLt {
            lt_lo: crate::twist::lt_table(&y[..h]),
            lt_hi: crate::twist::lt_table(&y[h..]),
            eq_hi: eq_table(&y[h..]),
            h,
        }
    }

    #[inline]
    pub(crate) fn at(&self, j: usize) -> K {
        let (lo, hi) = (j & ((1usize << self.h) - 1), j >> self.h);
        self.lt_hi[hi] + self.eq_hi[hi] * self.lt_lo[lo]
    }
}

/// `w ↦ Σ_{o < 2^ell} eq(r_o, o) · bit_o(w)` by byte-table lookup: the
/// MLE in the `o` variables of one word of a word table.
pub(crate) struct WordEval {
    tabs: Vec<[K; 256]>,
    mask: u64,
}

impl WordEval {
    /// # Panics
    /// Panics if `len(r_o) > 6` (words are `u64`).
    pub(crate) fn new(r_o: &[K]) -> Self {
        assert!(r_o.len() <= 6, "WordEval: ell must be <= 6");
        let eo = eq_table(r_o);
        let l = eo.len();
        let nbytes = l.div_ceil(8);
        let mut tabs = vec![[K::ZERO; 256]; nbytes];
        for (b, tab) in tabs.iter_mut().enumerate() {
            for v in 1..256usize {
                let low = v & (v - 1);
                let bit = v.trailing_zeros() as usize;
                let o = 8 * b + bit;
                tab[v] = tab[low] + if o < l { eo[o] } else { K::ZERO };
            }
        }
        let mask = if l >= 64 { u64::MAX } else { (1u64 << l) - 1 };
        WordEval { tabs, mask }
    }

    #[inline]
    pub(crate) fn eval(&self, w: u64) -> K {
        let w = w & self.mask;
        let mut acc = K::ZERO;
        for (b, tab) in self.tabs.iter().enumerate() {
            acc += tab[((w >> (8 * b)) & 0xff) as usize];
        }
        acc
    }
}

/// `Σ_j eq(r_c, j) · f(j)` over `j < 2^len(r_c)`.
pub(crate) fn eq_weighted_sum(r_c: &[K], f: &(dyn Fn(usize) -> K + Sync)) -> K {
    use om_field::U256;
    let t = 1usize << r_c.len();
    let se = SplitEq::new(r_c);
    let block = |hi_idx: usize| -> K {
        let base = hi_idx << se.h;
        let mut u = U256::ZERO;
        for (lo_idx, &e_lo) in se.lo.iter().enumerate() {
            u += e_lo.clmul(f(base | lo_idx));
        }
        se.hi[hi_idx] * u.reduce()
    };
    if t >= PAR_THRESHOLD {
        (0..se.hi.len())
            .into_par_iter()
            .map(block)
            .reduce(|| K::ZERO, |a, b| a + b)
    } else {
        (0..se.hi.len()).fold(K::ZERO, |acc, hi_idx| acc + block(hi_idx))
    }
}

/// A row function: `fill(j, out)` writes the `width` table entries of
/// row (cycle) `j` into `out`.
pub(crate) type RowFn<'a> = dyn Fn(usize, &mut [K]) + Sync + 'a;

/// Bound row of group `g` (size `2^r`, `eqw = eq_table(r_1..r_r)`):
/// `out = Σ_u eqw[u] · row(g·2^r + u)`.
fn bound_row(row: &RowFn<'_>, eqw: &[K], g: usize, out: &mut [K], scratch: &mut [K]) {
    let base = g * eqw.len();
    if eqw.len() == 1 {
        row(base, out);
        return;
    }
    if eqw.len() == 2 {
        let ch = eqw[1];
        row(base, out);
        row(base + 1, scratch);
        for (o, &s) in out.iter_mut().zip(scratch.iter()) {
            *o += ch * (*o + s);
        }
        return;
    }
    out.iter_mut().for_each(|v| *v = K::ZERO);
    for (u, &e) in eqw.iter().enumerate() {
        row(base + u, scratch);
        for (o, &s) in out.iter_mut().zip(scratch.iter()) {
            *o += e * s;
        }
    }
}

/// Exactly [`om_sumcheck::sumcheck_prove`] (same transcript, proof,
/// challenges and final table values) on the `width` tables of length
/// `2^n` whose row `j` is `row(j)`, with the honest claim
/// `Σ_j combine(row(j))`. The first rounds are computed from the rows
/// directly; the bound tables are materialised only once they have
/// shrunk by `2^DIRECT_ROUNDS`. Returns `(claim, proof, r, mles)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn sumcheck_prove_rows(
    n: usize,
    width: usize,
    row: &RowFn<'_>,
    combine: &(dyn Fn(&[K]) -> K + Sync),
    degree: usize,
    transcript: &mut Transcript,
    label: &[u8],
) -> (K, SumcheckProof, Vec<K>, Vec<K>) {
    assert!(degree >= 1, "degree must be >= 1");
    if n == 0 {
        let mut v = vec![K::ZERO; width];
        row(0, &mut v);
        let claim = combine(&v);
        sumcheck_init(transcript, label, claim, 0, degree);
        return (claim, SumcheckProof { round_msgs: vec![] }, vec![], v);
    }
    let msg_label = sublabel(label, b"/msg");
    let chal_label = sublabel(label, b"/chal");
    let mut msgs = Vec::with_capacity(n);
    let mut rs: Vec<K> = Vec::with_capacity(n);
    let (mut claim, mut cur) = (K::ZERO, K::ZERO);
    let direct = n.min(DIRECT_ROUNDS);
    for r in 0..direct {
        let eqw = eq_table(&rs);
        let half = 1usize << (n - r - 1);
        let pair = |acc: &mut Vec<K>, bufs: &mut [Vec<K>; 4], m: usize| {
            let [l, rr, vals, scratch] = bufs;
            bound_row(row, &eqw, 2 * m, l, scratch);
            bound_row(row, &eqw, 2 * m + 1, rr, scratch);
            acc[0] += combine(l);
            if degree >= 1 {
                acc[1] += combine(rr);
            }
            for (k, slot) in acc.iter_mut().enumerate().skip(2) {
                for i in 0..width {
                    vals[i] = l[i] + (l[i] + rr[i]).mul_t(k as u128);
                }
                *slot += combine(vals);
            }
        };
        let new_bufs = || -> [Vec<K>; 4] { std::array::from_fn(|_| vec![K::ZERO; width]) };
        let ev: Vec<K> = if (1usize << n) >= PAR_THRESHOLD {
            (0..half)
                .into_par_iter()
                .with_min_len(1024)
                .fold(
                    || (vec![K::ZERO; degree + 1], new_bufs()),
                    |(mut acc, mut bufs), m| {
                        pair(&mut acc, &mut bufs, m);
                        (acc, bufs)
                    },
                )
                .map(|(acc, _)| acc)
                .reduce(
                    || vec![K::ZERO; degree + 1],
                    |mut a, b| {
                        for (x, y) in a.iter_mut().zip(&b) {
                            *x += *y;
                        }
                        a
                    },
                )
        } else {
            let (mut acc, mut bufs) = (vec![K::ZERO; degree + 1], new_bufs());
            for m in 0..half {
                pair(&mut acc, &mut bufs, m);
            }
            acc
        };
        if r == 0 {
            claim = ev[0] + ev[1];
            cur = claim;
            sumcheck_init(transcript, label, claim, n, degree);
        }
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = Vec::with_capacity(degree);
        msg.push(ev[0]);
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let ch = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(ch);
        cur = interpolate_eval(&ev, ch);
    }
    // Materialise the bound tables (length 2^(n - direct)).
    let eqw = eq_table(&rs);
    let size = 1usize << (n - direct);
    let mut tables: Vec<Vec<K>> = vec![vec![K::ZERO; size]; width];
    {
        // Disjoint column pieces per chunk of groups, filled in parallel.
        const CH: usize = 1 << 10;
        let mut pieces: Vec<(usize, Vec<&mut [K]>)> = (0..size.div_ceil(CH))
            .map(|c| (c * CH, Vec::with_capacity(width)))
            .collect();
        for tb in &mut tables {
            for (c, part) in tb.chunks_mut(CH).enumerate() {
                pieces[c].1.push(part);
            }
        }
        let fill = |(g0, cols): (usize, Vec<&mut [K]>)| {
            let (mut out, mut scratch) = (vec![K::ZERO; width], vec![K::ZERO; width]);
            let mut cols = cols;
            for u in 0..cols[0].len() {
                bound_row(row, &eqw, g0 + u, &mut out, &mut scratch);
                for (col, &v) in cols.iter_mut().zip(&out) {
                    col[u] = v;
                }
            }
        };
        if (1usize << n) >= PAR_THRESHOLD {
            pieces.into_par_iter().for_each(fill);
        } else {
            pieces.into_iter().for_each(fill);
        }
    }
    for _ in direct..n {
        let ev = sumcheck_round_evals(&tables, combine, degree);
        assert_eq!(
            ev[0] + ev[1],
            cur,
            "claim inconsistent with tables (g(0)+g(1) != claim)"
        );
        let mut msg = Vec::with_capacity(degree);
        msg.push(ev[0]);
        msg.extend_from_slice(&ev[2..]);
        transcript.absorb_ks(&msg_label, &msg);
        let ch = transcript.challenge_k(&chal_label);
        msgs.push(msg);
        rs.push(ch);
        cur = interpolate_eval(&ev, ch);
        for t in &mut tables {
            bind_low_in_place(t, ch);
        }
    }
    let mles = tables.iter().map(|t| t[0]).collect();
    (claim, SumcheckProof { round_msgs: msgs }, rs, mles)
}

/// `f_t~(r_c) = Σ_j eq(r_c, j) · bit_t(addr(j))` for `t < a`, over
/// `j < 2^len(r_c)`.
pub(crate) fn addr_bit_evals(
    a: usize,
    r_c: &[K],
    addr: &(dyn Fn(usize) -> usize + Sync),
) -> Vec<K> {
    let t = 1usize << r_c.len();
    let se = SplitEq::new(r_c);
    let mask = if a >= usize::BITS as usize {
        usize::MAX
    } else {
        (1usize << a) - 1
    };
    let block = |hi_idx: usize| -> Vec<K> {
        let mut local = vec![0u128; a];
        let base = hi_idx << se.h;
        for (lo_idx, &e_lo) in se.lo.iter().enumerate() {
            let mut ad = addr(base | lo_idx) & mask;
            if ad == 0 {
                continue;
            }
            let ev = e_lo.value();
            while ad != 0 {
                let b = ad.trailing_zeros() as usize;
                local[b] ^= ev;
                ad &= ad - 1;
            }
        }
        let hi_v = se.hi[hi_idx];
        local
            .into_iter()
            .map(|v| {
                if v == 0 {
                    K::ZERO
                } else {
                    K::from_u128(v) * hi_v
                }
            })
            .collect()
    };
    if t >= PAR_THRESHOLD {
        (0..se.hi.len())
            .into_par_iter()
            .map(block)
            .reduce(
                || vec![K::ZERO; a],
                |mut x, y| {
                    for (p, q) in x.iter_mut().zip(&y) {
                        *p += *q;
                    }
                    x
                },
            )
    } else {
        (0..se.hi.len()).fold(vec![K::ZERO; a], |mut acc, hi_idx| {
            for (p, q) in acc.iter_mut().zip(block(hi_idx)) {
                *p += q;
            }
            acc
        })
    }
}
