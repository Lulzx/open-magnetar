//! Port of `reference/tests/test_shout.py`.

mod common;

use common::Rng;
use om_field::K;
use om_memcheck::onehot::comp_tables;
use om_memcheck::shout::{
    ShoutClaims, ShoutParams, ShoutProof, shout_honest_claims, shout_prove, shout_verify,
};
use om_sumcheck::mle_eval_bits;
use om_transcript::Transcript;

fn tr() -> Transcript {
    Transcript::new_default(b"test/shout")
}

type Made = (ShoutParams, Vec<Vec<K>>, Vec<usize>, Vec<Vec<bool>>, Vec<K>);

fn make(a: usize, d: usize, n: usize, c: usize, seed: u64) -> Made {
    let mut rng = Rng(seed);
    let (nk, t) = (1usize << a, 1usize << n);
    let table: Vec<Vec<K>> = (0..c)
        .map(|h| {
            (0..nk)
                .map(|_| {
                    if h == 0 {
                        rng.k()
                    } else {
                        K::from_bit(rng.bit())
                    }
                })
                .collect()
        })
        .collect();
    let addrs: Vec<usize> = (0..t).map(|_| rng.below(nk)).collect();
    let comps = comp_tables(&addrs, a, d);
    let r_c = rng.ks(n);
    (
        ShoutParams {
            name: "sh".to_string(),
            a,
            d,
            n,
        },
        table,
        addrs,
        comps,
        r_c,
    )
}

fn mle_of(table_col: &[K], addrs: &[usize], r_c: &[K]) -> K {
    // mle_eval([table[h][ad] for ad in addrs], r_c)
    let col: Vec<K> = addrs.iter().map(|&ad| table_col[ad]).collect();
    om_sumcheck::mle_eval(&col, r_c)
}

fn check_cfg(
    a: usize,
    d: usize,
    n: usize,
    c: usize,
    seed: u64,
) -> (
    ShoutParams,
    Vec<Vec<K>>,
    Vec<Vec<bool>>,
    ShoutClaims,
    ShoutProof,
) {
    let (p, table, addrs, comps, r_c) = make(a, d, n, c, seed);
    let claims = shout_honest_claims(&p, &table, &comps, &r_c, None, true);
    for (h, col) in table.iter().enumerate().take(c) {
        assert_eq!(claims.rv[h], mle_of(col, &addrs, &r_c));
    }
    let (proof, oc) = shout_prove(
        &p,
        &table,
        &comps,
        std::slice::from_ref(&claims),
        &mut tr(),
        b"S",
    );
    let vc = shout_verify(
        &p,
        &table,
        std::slice::from_ref(&claims),
        &proof,
        &mut tr(),
        b"S",
    )
    .unwrap();
    assert_eq!(oc, vc);
    for x in &vc {
        let i: usize = x.poly.rsplit('/').next().unwrap().parse::<usize>().unwrap() - 1;
        assert_eq!(mle_eval_bits(&comps[i], &x.point), x.value);
    }
    (p, table, comps, claims, proof)
}

#[test]
fn shout_d1() {
    check_cfg(3, 1, 3, 2, 1);
}

#[test]
fn shout_d2() {
    check_cfg(4, 2, 3, 3, 2);
}

#[test]
fn shout_d3() {
    check_cfg(6, 3, 2, 1, 3);
}

#[test]
fn multi_point_groups() {
    // Three claim groups at different cycle points, different column
    // subsets, one without address-bit claims.
    for (a, d) in [(4usize, 2usize), (3, 1)] {
        let (p, table, _addrs, comps, _r_c) = make(a, d, 3, 3, 9);
        let mut rng = Rng(10);
        let pts: Vec<Vec<K>> = (0..3).map(|_| rng.ks(3)).collect();
        let groups = vec![
            shout_honest_claims(&p, &table, &comps, &pts[0], None, true),
            shout_honest_claims(&p, &table, &comps, &pts[1], Some(&[1]), true),
            shout_honest_claims(&p, &table, &comps, &pts[2], Some(&[0, 2]), false),
        ];
        let (proof, oc) = shout_prove(&p, &table, &comps, &groups, &mut tr(), b"S");
        let vc = shout_verify(&p, &table, &groups, &proof, &mut tr(), b"S").unwrap();
        assert_eq!(oc, vc);
        for x in &vc {
            let i: usize = x.poly.rsplit('/').next().unwrap().parse::<usize>().unwrap() - 1;
            assert_eq!(mle_eval_bits(&comps[i], &x.point), x.value);
        }
        let mut bad = groups.clone();
        bad[1] = ShoutClaims {
            r_c: groups[1].r_c.clone(),
            cols: vec![1],
            rv: vec![groups[1].rv[0] + K::ONE],
            bits: groups[1].bits.clone(),
        };
        assert!(shout_verify(&p, &table, &bad, &proof, &mut tr(), b"S").is_err());
    }
}

#[test]
fn wrong_value() {
    let (p, table, _comps, claims, proof) = check_cfg(4, 2, 3, 2, 4);
    let bad = ShoutClaims {
        r_c: claims.r_c.clone(),
        cols: claims.cols.clone(),
        rv: vec![claims.rv[0] + K::ONE, claims.rv[1]],
        bits: claims.bits.clone(),
    };
    assert!(shout_verify(&p, &table, &[bad], &proof, &mut tr(), b"S").is_err());
}

#[test]
fn wrong_address_bit() {
    let (p, table, _comps, claims, proof) = check_cfg(4, 2, 3, 2, 5);
    let mut bits = claims.bits.clone().unwrap();
    bits[2] += K::ONE;
    let bad = ShoutClaims {
        bits: Some(bits),
        ..claims.clone()
    };
    assert!(shout_verify(&p, &table, &[bad], &proof, &mut tr(), b"S").is_err());
}

#[test]
fn hamming_two() {
    let (p, table, addrs, mut comps, r_c) = make(4, 2, 3, 2, 6);
    comps[0][1 + 4 * 2] = true;
    comps[0][2 + 4 * 2] = true;
    let good = comp_tables(&addrs, 4, 2);
    let claims = shout_honest_claims(&p, &table, &good, &r_c, None, true);
    let (proof, _) = shout_prove(
        &p,
        &table,
        &comps,
        std::slice::from_ref(&claims),
        &mut tr(),
        b"S",
    );
    assert!(shout_verify(&p, &table, &[claims], &proof, &mut tr(), b"S").is_err());
}

#[test]
fn hamming_zero() {
    let (p, table, addrs, mut comps, r_c) = make(4, 2, 3, 2, 7);
    for u in 0..4 {
        comps[1][u + 4 * 3] = false; // row j = 3 of component 2 is all-zero
    }
    let good = comp_tables(&addrs, 4, 2);
    let claims = shout_honest_claims(&p, &table, &good, &r_c, None, true);
    let (proof, _) = shout_prove(
        &p,
        &table,
        &comps,
        std::slice::from_ref(&claims),
        &mut tr(),
        b"S",
    );
    assert!(shout_verify(&p, &table, &[claims], &proof, &mut tr(), b"S").is_err());
}

#[test]
fn hamming_zero_d1() {
    let (p, table, addrs, mut comps, r_c) = make(3, 1, 3, 1, 8);
    for u in 0..8 {
        comps[0][u + 8 * 5] = false;
    }
    let good = comp_tables(&addrs, 3, 1);
    let claims = shout_honest_claims(&p, &table, &good, &r_c, None, true);
    let (proof, _) = shout_prove(
        &p,
        &table,
        &comps,
        std::slice::from_ref(&claims),
        &mut tr(),
        b"S",
    );
    assert!(shout_verify(&p, &table, &[claims], &proof, &mut tr(), b"S").is_err());
}
