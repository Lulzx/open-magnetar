//! Additive NTT / Reed–Solomon over K, novel polynomial basis (spec 04 §4.3).
//! Mirrors `reference/openmagnetar/ntt.py` exactly, including its `_WH` table
//! `ŵ[i][b] = Ŵ_i(β_b)` for `b ≥ i` (recomputed on demand here).

use om_field::K;
use rayon::prelude::*;

/// Codewords at least this large use rayon within `encode` stages.
const PAR_THRESHOLD: usize = 1 << 14;

fn wh_table(m: usize) -> Vec<Vec<K>> {
    let mut wh: Vec<Vec<K>> = Vec::with_capacity(m);
    let mut w: Vec<K> = (0..m).map(|b| K::from_u128(1u128 << b)).collect();
    for i in 0..m {
        let s = w[i];
        let sinv = s.inverse();
        let mut row = vec![K::ZERO; i];
        row.extend((i..m).map(|b| w[b] * sinv));
        wh.push(row);
        w = (0..m)
            .map(|b| if b > i { w[b] * (w[b] + s) } else { K::ZERO })
            .collect();
    }
    wh
}

/// `Ŵ_i(β_b)` (Python `what_beta`).
pub fn what_beta(i: usize, b: usize) -> K {
    let wh = wh_table(i.max(b) + 1);
    wh[i][b]
}

/// `[Ŵ_b(ω_q) for b < mu]`, for `q < 2^m` (Python `gen_weights`).
pub fn gen_weights(q: usize, mu: usize, m: usize) -> Vec<K> {
    let wh = wh_table(m);
    gen_weights_with(&wh, q, mu, m)
}

#[allow(clippy::needless_range_loop)]
fn gen_weights_with(wh: &[Vec<K>], q: usize, mu: usize, m: usize) -> Vec<K> {
    (0..mu)
        .map(|b| {
            let mut acc = 0u128;
            for c in b..m {
                if (q >> c) & 1 == 1 {
                    acc ^= wh[b][c].value();
                }
            }
            K::from_u128(acc)
        })
        .collect()
}

/// `[X_j(ω_q) for j < 2^mu]`, the generator-matrix column at position `q`.
pub fn basis_row(q: usize, mu: usize, m: usize) -> Vec<K> {
    let a = gen_weights(q, mu, m);
    let mut t = vec![K::ONE];
    for ab in a {
        let ext: Vec<K> = t.iter().map(|&e| e * ab).collect();
        t.extend(ext);
    }
    t
}

fn check_msg(msg: &[K]) -> usize {
    assert!(
        !msg.is_empty() && msg.len().is_power_of_two(),
        "message length must be a power of two"
    );
    msg.len().trailing_zeros() as usize
}

/// Naive `O(4^m)` encoding, evaluating the definition of §4.3.
///
/// # Panics
/// Panics if `msg.len()` is not a power of two.
pub fn encode_naive(msg: &[K], log_rate: usize) -> Vec<K> {
    let mu = check_msg(msg);
    let m = mu + log_rate;
    (0..1 << m)
        .map(|q| {
            msg.iter()
                .zip(basis_row(q, mu, m))
                .fold(K::ZERO, |acc, (&mj, g)| acc + mj * g)
        })
        .collect()
}

/// Fast `O(m 2^m)` LCH additive NTT encoding (§4.3):
/// `codeword[q] = Σ_j msg[j] X_j(ω_q)`.
///
/// # Panics
/// Panics if `msg.len()` is not a power of two.
pub fn encode(msg: &[K], log_rate: usize) -> Vec<K> {
    let mu = check_msg(msg);
    let m = mu + log_rate;
    let wh = wh_table(m);
    let mut a = vec![K::ZERO; 1 << m];
    a[..msg.len()].copy_from_slice(msg);
    for i in (0..m).rev() {
        let half = 1 << i;
        let blocks = 1usize << (m - 1 - i);
        let tks: Vec<K> = (0..blocks)
            .map(|c| {
                let mut t = 0u128;
                for d in 0..(m - 1 - i) {
                    if (c >> d) & 1 == 1 {
                        t ^= wh[i][i + 1 + d].value();
                    }
                }
                K::from_u128(t)
            })
            .collect();
        // Blocks of one stage touch disjoint pairs, as do the pairs within
        // a block, so either level parallelises exactly.
        let butterfly = |lo: &mut K, hi: &mut K, tk: K| {
            let new_lo = *lo + tk * *hi;
            *lo = new_lo;
            *hi += new_lo;
        };
        if a.len() >= PAR_THRESHOLD && blocks >= 4 {
            a.par_chunks_mut(2 * half)
                .zip(tks.par_iter())
                .for_each(|(block, &tk)| {
                    let (lo, hi) = block.split_at_mut(half);
                    for (l, h) in lo.iter_mut().zip(hi.iter_mut()) {
                        butterfly(l, h, tk);
                    }
                });
        } else if a.len() >= PAR_THRESHOLD && half >= 4096 {
            for (block, &tk) in a.chunks_mut(2 * half).zip(&tks) {
                let (lo, hi) = block.split_at_mut(half);
                lo.par_iter_mut()
                    .zip(hi.par_iter_mut())
                    .for_each(|(l, h)| butterfly(l, h, tk));
            }
        } else {
            for (block, &tk) in a.chunks_mut(2 * half).zip(&tks) {
                let (lo, hi) = block.split_at_mut(half);
                for (l, h) in lo.iter_mut().zip(hi.iter_mut()) {
                    butterfly(l, h, tk);
                }
            }
        }
    }
    a
}
