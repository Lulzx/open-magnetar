//! Port of `reference/tests/test_mle.py`.

use om_field::K;
use om_sumcheck::{bind_low, bind_low_in_place, eq_eval, eq_table, mle_eval, mle_eval_bits};

/// Small deterministic PRNG (xoshiro-style splitmix), test-only stand-in
/// for Python's `random.Random`.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn k(&mut self) -> K {
        K::from_u128(((self.next_u64() as u128) << 64) | self.next_u64() as u128)
    }
    fn bit(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

fn brute(table: &[K], r: &[K]) -> K {
    let mut acc = K::ZERO;
    for (i, &v) in table.iter().enumerate() {
        let bits: Vec<K> = (0..r.len())
            .map(|j| K::from_u128(((i >> j) & 1) as u128))
            .collect();
        acc += v * eq_eval(r, &bits);
    }
    acc
}

#[test]
fn test_eq_table() {
    let mut rng = Rng(3);
    let r: Vec<K> = (0..4).map(|_| rng.k()).collect();
    let t = eq_table(&r);
    assert_eq!(t.len(), 16);
    for (i, &ti) in t.iter().enumerate() {
        let bits: Vec<K> = (0..4)
            .map(|j| K::from_u128(((i >> j) & 1) as u128))
            .collect();
        assert_eq!(ti, eq_eval(&r, &bits));
    }
    let sum = t.iter().fold(K::ZERO, |a, &x| a + x);
    assert_eq!(sum, K::ONE);
}

#[test]
fn test_mle_eval_bruteforce() {
    let mut rng = Rng(4);
    for n in 0..6 {
        let r: Vec<K> = (0..n).map(|_| rng.k()).collect();
        let tk: Vec<K> = (0..1 << n).map(|_| rng.k()).collect();
        let tb: Vec<bool> = (0..1 << n).map(|_| rng.bit()).collect();
        let tbk: Vec<K> = tb.iter().map(|&b| K::from_bit(b)).collect();
        assert_eq!(mle_eval(&tk, &r), brute(&tk, &r), "n={n} K table");
        assert_eq!(mle_eval_bits(&tb, &r), brute(&tbk, &r), "n={n} bit table");
        assert_eq!(
            mle_eval(&tbk, &r),
            mle_eval_bits(&tb, &r),
            "n={n} bits as K"
        );
    }
}

#[test]
fn test_boolean_point_and_low_order() {
    let t: Vec<K> = (0..8).map(|i| K::from_u128(i + 1)).collect();
    // Index 5 = bits (1,0,1), x_1 is the LSB.
    assert_eq!(mle_eval(&t, &[K::ONE, K::ZERO, K::ONE]), t[5]);
    let r = [K::from_u128(7), K::from_u128(9), K::from_u128(11)];
    assert_eq!(mle_eval(&t, &r), mle_eval(&bind_low(&t, r[0]), &r[1..]));
}

#[test]
fn test_packing_identity() {
    // Ring-switching identities of spec 01.
    let mut rng = Rng(5);
    let l = 9;
    let w: Vec<bool> = (0..1 << l).map(|_| rng.bit()).collect();
    let p: Vec<K> = (0..1 << (l - 7))
        .map(|v| K::pack(&w[128 * v..128 * v + 128]))
        .collect();
    let r: Vec<K> = (0..l).map(|_| rng.k()).collect();
    let (rlo, rhi) = (&r[..7], &r[7..]);
    let s: Vec<K> = (0..128)
        .map(|j| {
            let col: Vec<bool> = (0..1 << (l - 7)).map(|v| w[j + 128 * v]).collect();
            mle_eval_bits(&col, rhi)
        })
        .collect();
    let e = eq_table(rlo);
    let lhs1: K = (0..128).fold(K::ZERO, |a, j| a + e[j] * s[j]);
    assert_eq!(mle_eval_bits(&w, &r), lhs1);
    let lhs2: K = (0..128).fold(K::ZERO, |a, j| a + K::from_u128(1u128 << j) * s[j]);
    assert_eq!(mle_eval(&p, rhi), lhs2);
}

#[test]
#[should_panic(expected = "length mismatch")]
fn test_eq_eval_length_mismatch_panics() {
    let _ = eq_eval(&[K::ONE], &[K::ONE, K::ZERO]);
}

#[test]
#[should_panic(expected = "table length must be 2^len(r)")]
fn test_mle_eval_wrong_length_panics() {
    let _ = mle_eval(&[K::ONE, K::ONE, K::ONE], &[K::ONE]);
}

#[test]
#[should_panic(expected = "table length must be even")]
fn test_bind_low_odd_panics() {
    let _ = bind_low(&[K::ONE, K::ONE, K::ONE], K::ONE);
}

#[test]
fn test_packed_bits_roundtrip() {
    let mut rng = Rng(3);
    for len in [0usize, 1, 63, 64, 65, 129, 1000] {
        let bits: Vec<bool> = (0..len).map(|_| rng.bit()).collect();
        let packed = om_sumcheck::PackedBits::from_bools(&bits);
        assert_eq!(packed.len(), len);
        assert_eq!(packed.to_bools(), bits, "len={len}");
        let ones: Vec<usize> = bits
            .iter()
            .enumerate()
            .filter_map(|(i, &b)| b.then_some(i))
            .collect();
        assert_eq!(packed.iter_ones().collect::<Vec<_>>(), ones, "len={len}");
        assert_eq!(packed.count_ones(), ones.len());
        if len > 0 && len.is_power_of_two() {
            let r: Vec<K> = (0..len.trailing_zeros()).map(|_| rng.k()).collect();
            assert_eq!(
                om_sumcheck::mle_eval_packed(&packed, &r),
                mle_eval_bits(&bits, &r),
                "len={len}"
            );
        }
    }
}

#[test]
fn test_bind_low_in_place_matches() {
    let mut rng = Rng(9);
    for n in 1..=8usize {
        let t: Vec<K> = (0..1 << n).map(|_| rng.k()).collect();
        let r = rng.k();
        let want = bind_low(&t, r);
        let mut got = t.clone();
        bind_low_in_place(&mut got, r);
        assert_eq!(got, want, "n={n}");
        // Repeated in-place binding agrees with repeated bind_low.
        let (mut a, mut b) = (t.clone(), t);
        for _ in 0..n {
            let r = rng.k();
            a = bind_low(&a, r);
            bind_low_in_place(&mut b, r);
        }
        assert_eq!(a, b, "n={n} fully bound");
    }
}
