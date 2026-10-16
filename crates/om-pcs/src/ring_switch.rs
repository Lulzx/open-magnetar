//! Ring switching for the monomial packing basis `β_j = X^j` (spec 04 §4.5).
//! Mirrors `reference/openmagnetar/ring_switch.py`.
//!
//! Reduces `w̃(r) = y` for a bit vector of length `2^ℓ` (`ℓ ≥ 8`) to
//! `P̃(r_s) = v` for the packed vector of length `2^(ℓ-7)`.

use om_field::K;
use om_sumcheck::{
    PackedBits, SumcheckProof, VerificationError, eq_table, sumcheck_prove, sumcheck_verify,
};
use om_transcript::Transcript;
use rayon::prelude::*;

/// Tables at least this large use rayon (exact elementwise maps).
const PAR_THRESHOLD: usize = 1 << 14;

/// `κ = 7` (§4.5).
pub const KAPPA: usize = 7;
/// Packing width `128 = 2^κ` (Python `W`).
pub const W: usize = 1 << KAPPA;

/// `RingSwitchProof = (s, sum-check messages)` (§4.5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchProof {
    /// The 128 partial evaluations `s_j`.
    pub s: Vec<K>,
    /// The sum-check proof (`ℓ-7` rounds, degree 2).
    pub sumcheck: SumcheckProof,
}

/// `P[v] = Σ_j X^j · bits[j + 128v]` (§4.5, C1 packing).
///
/// # Panics
/// Panics if `bits.len()` is not a multiple of 128 (Python `ValueError`).
pub fn pack(bits: &[bool]) -> Vec<K> {
    assert!(
        bits.len().is_multiple_of(W),
        "bit vector length must be a multiple of 128"
    );
    if bits.len() >= PAR_THRESHOLD {
        bits.par_chunks(W).map(K::pack).collect()
    } else {
        bits.chunks(W).map(K::pack).collect()
    }
}

/// [`pack`] from packed words: word pair `(lo, hi)` is the packed
/// element `K(hi · 2^64 + lo)`, the same value `K::pack` produces
/// from the corresponding 128 bools.
///
/// # Panics
/// If the packed length is not a multiple of 128.
pub fn pack_packed(bits: &PackedBits) -> Vec<K> {
    assert!(
        bits.len().is_multiple_of(W),
        "bit vector length must be a multiple of 128"
    );
    let words = bits.words();
    let pair_to_k = |pair: &[u64]| {
        let lo = u128::from(pair[0]);
        let hi = pair.get(1).map_or(0, |&h| u128::from(h));
        K::from_u128(lo | (hi << 64))
    };
    if bits.len() >= PAR_THRESHOLD {
        words.par_chunks(2).map(pair_to_k).collect()
    } else {
        words.chunks(2).map(pair_to_k).collect()
    }
}

/// [`partial_evals`] from packed bits: only set bits are visited, and the
/// high eq factor `hi[vh]` is multiplied once per 128-entry block rather than
/// on every `vl`.
///
/// # Panics
/// If the packed length is not a multiple of 128.
pub fn partial_evals_packed(bits: &PackedBits, r_hi: &[K]) -> Vec<K> {
    assert!(
        bits.len().is_multiple_of(W),
        "bit vector length must be a multiple of 128"
    );
    // eq(r_hi, v) = lo[v_lo] * hi[v_hi]: two square-root tables
    // instead of one of 2^len(r_hi) entries.
    let h = r_hi.len() / 2;
    let (lo, hi) = (eq_table(&r_hi[..h]), eq_table(&r_hi[h..]));
    let words = bits.words();
    let block = |vh: usize| -> [u128; W] {
        let mut local = [0u128; W];
        let v_base = vh << h;
        for (vl, e_lo) in lo.iter().enumerate() {
            let v = v_base | vl;
            let w0 = words[2 * v];
            let w1 = words[2 * v + 1];
            if (w0 | w1) == 0 {
                continue;
            }
            let e = e_lo.value();
            let mut m0 = w0;
            while m0 != 0 {
                let b = m0.trailing_zeros() as usize;
                m0 &= m0 - 1;
                local[b] ^= e;
            }
            let mut m1 = w1;
            while m1 != 0 {
                let b = m1.trailing_zeros() as usize;
                m1 &= m1 - 1;
                local[64 + b] ^= e;
            }
        }
        let hi_v = hi[vh];
        let mut acc = [0u128; W];
        for i in 0..W {
            if local[i] != 0 {
                acc[i] = (K::from_u128(local[i]) * hi_v).value();
            }
        }
        acc
    };
    let merge = |mut a: [u128; W], b: [u128; W]| {
        for (x, y) in a.iter_mut().zip(b) {
            *x ^= y;
        }
        a
    };
    let acc = if bits.len() >= PAR_THRESHOLD {
        (0..hi.len())
            .into_par_iter()
            .map(block)
            .reduce(|| [0u128; W], merge)
    } else {
        (0..hi.len()).map(block).fold([0u128; W], merge)
    };
    acc.into_iter().map(K::from_u128).collect()
}

/// [`rs_prove`] over packed bits: the same proof, without expanding
/// the bit vector.
///
/// # Panics
/// As [`rs_prove`].
pub fn rs_prove_packed(
    bits: &PackedBits,
    r: &[K],
    y: K,
    tr: &mut Transcript,
) -> (RingSwitchProof, Vec<K>, K) {
    let s = partial_evals_packed_checked(bits, r);
    rs_prove_from_s(bits, r, y, s, tr)
}

/// [`rs_prove_packed`] that also returns the value `y = w~(r)`,
/// computed from the partial evaluations as `sum_j eq(r_lo, j) s_j`
/// (the identity the verifier checks) instead of from a table over
/// all `2^ell` positions. Returns `(proof, r_s, v, y)`.
///
/// # Panics
/// As [`rs_prove_packed`].
pub fn rs_prove_packed_value(
    bits: &PackedBits,
    r: &[K],
    tr: &mut Transcript,
) -> (RingSwitchProof, Vec<K>, K, K) {
    let s = partial_evals_packed_checked(bits, r);
    let y = eq_table(&r[..KAPPA])
        .iter()
        .zip(&s)
        .fold(K::ZERO, |acc, (&e, &sj)| acc + e * sj);
    let (proof, r_s, v) = rs_prove_from_s(bits, r, y, s, tr);
    (proof, r_s, v, y)
}

fn partial_evals_packed_checked(bits: &PackedBits, r: &[K]) -> Vec<K> {
    let ell = r.len();
    assert!(
        ell > KAPPA && bits.len() == 1 << ell,
        "need ell >= 8 and 2^ell bits"
    );
    partial_evals_packed(bits, &r[KAPPA..])
}

fn rs_prove_from_s(
    bits: &PackedBits,
    r: &[K],
    y: K,
    s: Vec<K>,
    tr: &mut Transcript,
) -> (RingSwitchProof, Vec<K>, K) {
    absorb_claim(tr, r, y);
    tr.absorb_ks(b"rs/s", &s);
    let rho = tr.challenge_ks(b"rs/rho", KAPPA);
    let target = target_of(&s, &rho);
    let a = a_table(&r[KAPPA..], &rho);
    let p = pack_packed(bits);
    let (proof, r_s, finals) = sumcheck_prove(
        target,
        vec![p, a],
        &|v: &[K]| v[0] * v[1],
        2,
        tr,
        b"rs/sumcheck",
    );
    (RingSwitchProof { s, sumcheck: proof }, r_s, finals[0])
}

/// `s_j = Σ_v eq(r_hi, v) · bits[j + 128v]`.
pub fn partial_evals(bits: &[bool], r_hi: &[K]) -> Vec<K> {
    let eqt = eq_table(r_hi);
    let at = |j: usize| {
        let mut acc = 0u128;
        for (v, e) in eqt.iter().enumerate() {
            if bits[j + W * v] {
                acc ^= e.value();
            }
        }
        K::from_u128(acc)
    };
    if bits.len() >= PAR_THRESHOLD {
        (0..W).into_par_iter().map(at).collect()
    } else {
        (0..W).map(at).collect()
    }
}

/// `c_i = pack_j(bit_i(s_j))` (left coordinates → right coordinates).
pub fn transpose_bits(s: &[K]) -> Vec<K> {
    (0..W)
        .map(|i| {
            let mut v = 0u128;
            for (j, sj) in s.iter().enumerate().take(W) {
                v |= ((sj.value() >> i) & 1) << j;
            }
            K::from_u128(v)
        })
        .collect()
}

/// `a[v] = Σ_i eq(ρ, i) · bit_i(eq(r_hi, v))`.
pub fn a_table(r_hi: &[K], rho: &[K]) -> Vec<K> {
    let er: Vec<u128> = eq_table(rho).iter().map(|e| e.value()).collect();
    let mut base_lut = [[0u128; 256]; 16];
    for (byte_idx, table) in base_lut.iter_mut().enumerate() {
        for b in 1..256usize {
            let bit = b.trailing_zeros() as usize;
            let idx = 8 * byte_idx + bit;
            let val = if idx < er.len() { er[idx] } else { 0 };
            table[b] = table[b & (b - 1)] ^ val;
        }
    }
    let eval_l = |z: u128| -> u128 {
        let bytes = z.to_le_bytes();
        let mut acc = 0u128;
        for (byte_idx, &b) in bytes.iter().enumerate() {
            acc ^= base_lut[byte_idx][b as usize];
        }
        acc
    };

    let n = 1usize << r_hi.len();
    if r_hi.len() >= 14 {
        // Since L(z) = Σ_i eq(ρ, i) bit_i(z) is GF(2)-linear in z, for each
        // fixed y = hi[v_hi] the composite map x ↦ L(x · y) is GF(2)-linear
        // in x = lo[v_lo]. Building a 16-byte LUT per `v_hi` eliminates all
        // 2^len(r_hi) field multiplications.
        let h_lo = (r_hi.len() - 6).clamp(10, 18);
        let (lo, hi) = (eq_table(&r_hi[..h_lo]), eq_table(&r_hi[h_lo..]));
        let lo_len = 1usize << h_lo;
        let mut out = vec![K::ZERO; n];
        out.par_chunks_mut(lo_len)
            .zip(hi.par_iter())
            .for_each(|(chunk, &y)| {
                let mut lut_y = [[0u128; 256]; 16];
                for (byte_idx, table) in lut_y.iter_mut().enumerate() {
                    let mut basis = [0u128; 8];
                    for (bit, b_val) in basis.iter_mut().enumerate() {
                        let k = 8 * byte_idx + bit;
                        let prod = (K::from_u128(1u128 << k) * y).value();
                        *b_val = eval_l(prod);
                    }
                    for b in 1..256usize {
                        let bit = b.trailing_zeros() as usize;
                        table[b] = table[b & (b - 1)] ^ basis[bit];
                    }
                }
                for (dst, &x) in chunk.iter_mut().zip(&lo) {
                    let bytes = x.value().to_le_bytes();
                    let mut acc = 0u128;
                    for (byte_idx, &b) in bytes.iter().enumerate() {
                        acc ^= lut_y[byte_idx][b as usize];
                    }
                    *dst = K::from_u128(acc);
                }
            });
        return out;
    }

    // Small tables: eq(r_hi, v) = lo[v_lo] * hi[v_hi] per entry.
    let h = r_hi.len() / 2;
    let (lo, hi) = (eq_table(&r_hi[..h]), eq_table(&r_hi[h..]));
    let mask = (1usize << h) - 1;
    let at = |v: usize| K::from_u128(eval_l((lo[v & mask] * hi[v >> h]).value()));
    if n >= PAR_THRESHOLD {
        (0..n).into_par_iter().map(at).collect()
    } else {
        (0..n).map(at).collect()
    }
}

fn mul_tensor(t: &[K], x: K, y: K) -> Vec<K> {
    let mut acc = [0u128; W];
    for (i, ti) in t.iter().enumerate() {
        if ti.is_zero() {
            continue;
        }
        let mut xb = (x * K::from_u128(1u128 << i)).value();
        let mut m = 0usize;
        while xb != 0 {
            if xb & 1 == 1 {
                acc[m] ^= ti.value();
            }
            xb >>= 1;
            m += 1;
        }
    }
    acc.iter().map(|&a| K::from_u128(a) * y).collect()
}

/// MLE of `a` at `z` via the tensor recursion of §4.5 step 5:
/// `T = Π_u [(1+r_u)⊗(1+z_u) + r_u⊗z_u]`.
pub fn a_eval(r_hi: &[K], rho: &[K], z: &[K]) -> K {
    let mut t = vec![K::ZERO; W];
    t[0] = K::ONE;
    for (&rk, &zk) in r_hi.iter().zip(z) {
        let t1 = mul_tensor(&t, K::ONE + rk, K::ONE + zk);
        let t2 = mul_tensor(&t, rk, zk);
        t = t1.iter().zip(&t2).map(|(&p, &q)| p + q).collect();
    }
    eq_table(rho)
        .iter()
        .zip(&t)
        .fold(K::ZERO, |acc, (&e, &ti)| acc + e * ti)
}

fn absorb_claim(tr: &mut Transcript, r: &[K], y: K) {
    tr.absorb_ks(b"rs/point", r);
    tr.absorb_k(b"rs/value", y);
}

fn target_of(s: &[K], rho: &[K]) -> K {
    let c = transpose_bits(s);
    eq_table(rho)
        .iter()
        .zip(&c)
        .fold(K::ZERO, |acc, (&e, &ci)| acc + e * ci)
}

/// Prover. Returns `(proof, r_s, v)` with `v = P̃(r_s)`; the caller then
/// proves it with the PCS on the same transcript.
///
/// # Panics
/// Panics unless `ℓ ≥ 8` and `bits.len() == 2^ℓ` (Python `ValueError`).
pub fn rs_prove(bits: &[bool], r: &[K], y: K, tr: &mut Transcript) -> (RingSwitchProof, Vec<K>, K) {
    let ell = r.len();
    assert!(
        ell > KAPPA && bits.len() == 1 << ell,
        "need ell >= 8 and 2^ell bits"
    );
    let p = pack(bits);
    let s = partial_evals(bits, &r[KAPPA..]);
    absorb_claim(tr, r, y);
    tr.absorb_ks(b"rs/s", &s);
    let rho = tr.challenge_ks(b"rs/rho", KAPPA);
    let target = target_of(&s, &rho);
    let a = a_table(&r[KAPPA..], &rho);
    let (proof, r_s, finals) = sumcheck_prove(
        target,
        vec![p, a],
        &|v: &[K]| v[0] * v[1],
        2,
        tr,
        b"rs/sumcheck",
    );
    (RingSwitchProof { s, sumcheck: proof }, r_s, finals[0])
}

/// Verifier. Returns `(r_s, v)`: the PCS must now certify `P̃(r_s) = v`.
///
/// # Errors
/// Returns [`VerificationError`] on a too-small point, a malformed `s`, an
/// `s` inconsistent with `y`, a failed sum-check, or `ã(r_s) = 0` (§4.5).
pub fn rs_verify(
    r: &[K],
    y: K,
    proof: &RingSwitchProof,
    tr: &mut Transcript,
) -> Result<(Vec<K>, K), VerificationError> {
    let ell = r.len();
    if ell <= KAPPA {
        return Err(VerificationError::new("ell too small"));
    }
    if proof.s.len() != W {
        return Err(VerificationError::new("s must have 128 entries"));
    }
    absorb_claim(tr, r, y);
    let acc = eq_table(&r[..KAPPA])
        .iter()
        .zip(&proof.s)
        .fold(K::ZERO, |acc, (&e, &sj)| acc + e * sj);
    if acc != y {
        return Err(VerificationError::new(
            "ring switching: s inconsistent with claimed value",
        ));
    }
    tr.absorb_ks(b"rs/s", &proof.s);
    let rho = tr.challenge_ks(b"rs/rho", KAPPA);
    let target = target_of(&proof.s, &rho);
    let (r_s, final_claim) =
        sumcheck_verify(target, ell - KAPPA, 2, &proof.sumcheck, tr, b"rs/sumcheck")?;
    let a_val = a_eval(&r[KAPPA..], &rho, &r_s);
    if a_val.is_zero() {
        return Err(VerificationError::new(
            "ring switching: degenerate a(r_s) = 0",
        ));
    }
    Ok((r_s, final_claim / a_val))
}
