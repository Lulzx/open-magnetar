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
    basis_from_weights(&a)
}

fn basis_from_weights(a: &[K]) -> Vec<K> {
    let mut t = Vec::with_capacity(1usize << a.len());
    t.push(K::ONE);
    for &ab in a {
        let len = t.len();
        for i in 0..len {
            t.push(t[i] * ab);
        }
    }
    t
}

/// Split `basis_row(q, mu, m)` into `(lo, hi)` tensor factors of lengths
/// `2^(mu/2)` and `2^(mu - mu/2)` for each `q` in `qs`, sharing one `_WH` table.
pub fn split_basis_rows(qs: &[usize], mu: usize, m: usize) -> Vec<(Vec<K>, Vec<K>)> {
    let wh = wh_table(m);
    let mu_lo = mu / 2;
    qs.iter()
        .map(|&q| {
            let a = gen_weights_with(&wh, q, mu, m);
            (
                basis_from_weights(&a[..mu_lo]),
                basis_from_weights(&a[mu_lo..]),
            )
        })
        .collect()
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

/// Tile size (in `K` elements = 16 bytes each) for fusing the bottom NTT
/// stages inside L2 cache: `32,768 * 16 B = 512 KiB`.
const TILE_ELEMS: usize = 1 << 15;

/// Fast `O(m 2^m)` LCH additive NTT encoding (§4.3):
/// `codeword[q] = Σ_j msg[j] X_j(ω_q)`.
///
/// # Panics
/// Panics if `msg.len()` is not a power of two.
pub fn encode(msg: &[K], log_rate: usize) -> Vec<K> {
    let _mu = check_msg(msg);
    let cols = msg.len();
    let num_cosets = 1usize << log_rate;
    let mut a = Vec::with_capacity(cols << log_rate);
    for coset in 0..num_cosets {
        let start = a.len();
        a.extend_from_slice(msg);
        encode_coset_col_major(&mut a[start..start + cols], 1, cols, log_rate, coset);
    }
    a
}

/// In-place additive NTT encoding of one coset (`coset < 2^log_rate`) of a
/// column-major `rows × cols` matrix `buf` (`buf[row + rows * j]`).
///
/// On entry, `buf` holds the unencoded matrix `f` of length `rows * cols`.
/// On exit, `buf[row + rows * q_local]` holds `cw[row][coset * cols + q_local]`,
/// so each encoded column `q = coset * cols + q_local` is contiguous at
/// `&buf[q_local * rows .. (q_local + 1) * rows]`.
pub fn encode_coset_col_major(
    buf: &mut [K],
    rows: usize,
    cols: usize,
    log_rate: usize,
    coset: usize,
) {
    assert!(
        rows.is_power_of_two() && cols.is_power_of_two() && buf.len() == rows * cols,
        "encode_coset_col_major: dimensions must be powers of two matching buf.len()"
    );
    let mu = cols.trailing_zeros() as usize;
    if mu == 0 {
        return;
    }
    let m = mu + log_rate;
    let wh = wh_table(m);

    // Precompute coset contribution `t_coset[i]` for each stage `i < mu`.
    let t_cosets: Vec<u128> = (0..mu)
        .map(|i| {
            let mut t = 0u128;
            for d_hi in 0..log_rate {
                if (coset >> d_hi) & 1 == 1 {
                    t ^= wh[i][mu + d_hi].value();
                }
            }
            t
        })
        .collect();

    // Determine how many bottom stages `0..i_tile` fit inside a single L2 cache tile
    // of size `TILE_ELEMS` (when the buffer is large enough to benefit from parallel tiles).
    let i_tile = if buf.len() >= TILE_ELEMS * 2 && rows <= TILE_ELEMS / 2 {
        ((TILE_ELEMS / rows).trailing_zeros() as usize).min(mu)
    } else {
        0
    };

    // 1. Top stages `i in (i_tile..mu).rev()`, where block size `2 * half > TILE_ELEMS`.
    for i in (i_tile..mu).rev() {
        let half = (1usize << i) * rows;
        let blocks = 1usize << (mu - 1 - i);
        let t_coset = t_cosets[i];
        let tks: Vec<K> = (0..blocks)
            .map(|c_local| {
                let mut t = t_coset;
                for d_lo in 0..(mu - 1 - i) {
                    if (c_local >> d_lo) & 1 == 1 {
                        t ^= wh[i][i + 1 + d_lo].value();
                    }
                }
                K::from_u128(t)
            })
            .collect();
        if buf.len() >= PAR_THRESHOLD && blocks >= 4 {
            buf.par_chunks_mut(2 * half)
                .zip(tks.par_iter())
                .for_each(|(block, &tk)| {
                    let (lo, hi) = block.split_at_mut(half);
                    if tk == K::ZERO {
                        for (l, h) in lo.iter().zip(hi.iter_mut()) {
                            *h += *l;
                        }
                    } else {
                        for (l, h) in lo.iter_mut().zip(hi.iter_mut()) {
                            let new_lo = *l + tk * *h;
                            *l = new_lo;
                            *h += new_lo;
                        }
                    }
                });
        } else if buf.len() >= PAR_THRESHOLD && half >= 4096 {
            for (block, &tk) in buf.chunks_mut(2 * half).zip(&tks) {
                let (lo, hi) = block.split_at_mut(half);
                if tk == K::ZERO {
                    lo.par_chunks(4096)
                        .zip(hi.par_chunks_mut(4096))
                        .for_each(|(lc, hc)| {
                            for (l, h) in lc.iter().zip(hc.iter_mut()) {
                                *h += *l;
                            }
                        });
                } else {
                    lo.par_chunks_mut(4096)
                        .zip(hi.par_chunks_mut(4096))
                        .for_each(|(lc, hc)| {
                            for (l, h) in lc.iter_mut().zip(hc.iter_mut()) {
                                let new_lo = *l + tk * *h;
                                *l = new_lo;
                                *h += new_lo;
                            }
                        });
                }
            }
        } else {
            for (block, &tk) in buf.chunks_mut(2 * half).zip(&tks) {
                let (lo, hi) = block.split_at_mut(half);
                if tk == K::ZERO {
                    for (l, h) in lo.iter().zip(hi.iter_mut()) {
                        *h += *l;
                    }
                } else {
                    for (l, h) in lo.iter_mut().zip(hi.iter_mut()) {
                        let new_lo = *l + tk * *h;
                        *l = new_lo;
                        *h += new_lo;
                    }
                }
            }
        }
    }

    // 2. Bottom stages `i in (0..i_tile).rev()` fused inside L2-sized tiles.
    if i_tile > 0 {
        let tile_len = (1usize << i_tile) * rows;
        let t_subs: Vec<Vec<u128>> = (0..i_tile)
            .map(|i| {
                let s = i_tile - 1 - i;
                (0..(1usize << s))
                    .map(|sb| {
                        let mut t = 0u128;
                        for d_lo in 0..s {
                            if (sb >> d_lo) & 1 == 1 {
                                t ^= wh[i][i + 1 + d_lo].value();
                            }
                        }
                        t
                    })
                    .collect()
            })
            .collect();

        buf.par_chunks_mut(tile_len)
            .enumerate()
            .for_each(|(tile_idx, tile)| {
                for i in (0..i_tile).rev() {
                    let half = (1usize << i) * rows;
                    let mut t_tile = t_cosets[i];
                    for d_tile in 0..(mu - i_tile) {
                        if (tile_idx >> d_tile) & 1 == 1 {
                            t_tile ^= wh[i][i_tile + d_tile].value();
                        }
                    }
                    for (block, &t_sb) in tile.chunks_mut(2 * half).zip(&t_subs[i]) {
                        let tk = K::from_u128(t_tile ^ t_sb);
                        let (lo, hi) = block.split_at_mut(half);
                        if tk == K::ZERO {
                            for (l, h) in lo.iter().zip(hi.iter_mut()) {
                                *h += *l;
                            }
                        } else {
                            for (l, h) in lo.iter_mut().zip(hi.iter_mut()) {
                                let new_lo = *l + tk * *h;
                                *l = new_lo;
                                *h += new_lo;
                            }
                        }
                    }
                }
            });
    }
}
