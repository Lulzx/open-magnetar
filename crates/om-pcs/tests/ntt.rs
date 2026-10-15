//! Port of `reference/tests/test_ntt.py`.

mod common;

use common::Rng;
use om_field::K;
use om_pcs::ntt;

#[test]
fn fast_equals_naive() {
    let mut rng = Rng(7);
    for (mu, r) in [
        (0usize, 1usize),
        (1, 1),
        (2, 2),
        (3, 1),
        (4, 2),
        (5, 1),
        (3, 0),
    ] {
        let msg = rng.ks(1 << mu);
        assert_eq!(
            ntt::encode(&msg, r),
            ntt::encode_naive(&msg, r),
            "({mu}, {r})"
        );
    }
}

#[test]
fn linear() {
    let mut rng = Rng(8);
    let (a, b) = (rng.ks(8), rng.ks(8));
    let s = rng.k();
    let lhs = ntt::encode(
        &a.iter()
            .zip(&b)
            .map(|(&x, &y)| x + s * y)
            .collect::<Vec<_>>(),
        2,
    );
    let (ea, eb) = (ntt::encode(&a, 2), ntt::encode(&b, 2));
    assert_eq!(
        lhs,
        ea.iter()
            .zip(&eb)
            .map(|(&x, &y)| x + s * y)
            .collect::<Vec<_>>()
    );
}

#[test]
fn normalisation() {
    for i in 0..6 {
        assert_eq!(ntt::what_beta(i, i), K::ONE);
    }
}

#[test]
fn degree_bound_is_rs() {
    let mut rng = Rng(9);
    let msg = rng.ks(4);
    let (c1, c3) = (ntt::encode(&msg, 1), ntt::encode(&msg, 3));
    assert_eq!(c1, c3[..c1.len()], "U_m nested: prefix of the domain");
}

#[test]
fn minimum_distance() {
    let mut rng = Rng(10);
    let msg = rng.ks(8);
    let zeros = ntt::encode(&msg, 1).iter().filter(|x| x.is_zero()).count();
    assert!(zeros < 8, "nonzero poly of degree < 8 has < 8 roots");
}

#[test]
fn monomials() {
    // X_0 = 1, X_1 = Ŵ_0(x) = x.
    assert_eq!(
        ntt::encode(&[K::ZERO, K::ONE], 1),
        (0..4).map(K::t).collect::<Vec<_>>()
    );
}
