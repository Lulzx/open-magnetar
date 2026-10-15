//! Port of `reference/tests/test_onehot.py`.

mod common;

use common::Rng;
use om_field::K;
use om_memcheck::onehot::{
    EvalClaim, VirtGroup, VirtTerm, comp_tables, full_table, onehot_aux, onehot_prove,
    onehot_verify, split_addr, virt_prove, virt_verify,
};
use om_sumcheck::{eq_eval, eq_table, mle_eval_bits};
use om_transcript::Transcript;

fn tr() -> Transcript {
    Transcript::new_default(b"test/onehot")
}

#[test]
fn chunks_low_first() {
    assert_eq!(split_addr(0b110101, 6, 2), vec![0b101, 0b110]);
    assert_eq!(split_addr(0b110101, 6, 3), vec![0b01, 0b01, 0b11]);
}

#[test]
fn full_table_is_product() {
    let (a, d) = (4, 2);
    let addrs = [3usize, 12, 0, 15];
    let comps = comp_tables(&addrs, a, d);
    let full = full_table(&comps, a, d, 4);
    for (j, &ad) in addrs.iter().enumerate() {
        for k in 0..16 {
            assert_eq!(full[k + 16 * j], k == ad);
        }
    }
}

#[test]
fn eq_cubed() {
    // eq(r,u)^3 = C(r) eq(r',u) for Boolean u (characteristic 2)
    let mut rng = Rng(7);
    for ac in [1usize, 2, 3, 4] {
        let r = rng.ks(ac);
        let (rp, c) = onehot_aux(&r).expect("random r has c_h != 0");
        for u in 0..(1u64 << ac) {
            let ub: Vec<K> = (0..ac).map(|i| K::from_bit((u >> i) & 1 == 1)).collect();
            let e = eq_eval(&r, &ub);
            assert_eq!(e * e * e, c * eq_eval(&rp, &ub));
        }
    }
}

#[test]
fn delta_star_formula() {
    // Delta*(j; r) = A~(r)^3 + C A~(r') equals the collision polynomial
    // A~(r) A~(r^2) + sum_u A(u) eq(r,u) eq(r^2,u) for bit rows.
    let mut rng = Rng(8);
    let ac = 3usize;
    for _ in 0..20 {
        let row: Vec<bool> = (0..1 << ac).map(|_| rng.bit()).collect();
        let r = rng.ks(ac);
        let (rp, c) = onehot_aux(&r).unwrap();
        let s: Vec<K> = r.iter().map(|&x| x * x).collect();
        let at = mle_eval_bits(&row, &r);
        let (er, es) = (eq_table(&r), eq_table(&s));
        let mut diag = K::ZERO;
        for u in 0..1 << ac {
            if row[u] {
                diag += er[u] * es[u];
            }
        }
        let delta = at * mle_eval_bits(&row, &s) + diag;
        let star = at * at * at + c * mle_eval_bits(&row, &rp);
        assert_eq!(delta, star);
        assert_eq!(mle_eval_bits(&row, &s), at * at); // Frobenius
        let weight = row.iter().filter(|&&b| b).count();
        if weight <= 1 {
            assert_eq!(star, K::ZERO);
        } else {
            assert_ne!(star, K::ZERO);
        }
    }
}

#[test]
fn zero_c_detected() {
    // Primitive cube root of unity in GF(4) inside GF(2^128):
    // c = 1 + w + w^2 = 0. w = X^((2^128-1)/3); the exponent does not
    // fit the u128 pow, so use pow_limbs (little-endian 64-bit limbs).
    let e = (u128::MAX) / 3; // (2^128 - 1) / 3 fits in u128
    let w = K::X.pow(e);
    assert_eq!(K::ONE + w + w * w, K::ZERO);
    assert!(onehot_aux(&[K::ONE, w]).is_none());
    assert!(onehot_aux(&[K::ONE, K::X]).is_some());
}

fn run_check(
    comps: &[Vec<bool>],
    ac: usize,
    n: usize,
) -> Result<(Vec<EvalClaim>, Vec<EvalClaim>), om_sumcheck::VerificationError> {
    let names: Vec<String> = (0..comps.len()).map(|i| format!("c{i}")).collect();
    let (mut t1, mut t2) = (tr(), tr());
    let (proof, claims) = onehot_prove(comps, &names, ac, n, &mut t1, b"oh");
    let vclaims = onehot_verify(&names, ac, n, &proof, &mut t2, b"oh")?;
    Ok((claims, vclaims))
}

#[test]
fn onehot_honest() {
    let mut rng = Rng(3);
    let (n, ac) = (3usize, 3usize);
    let comps: Vec<Vec<bool>> = (0..3)
        .map(|_| {
            let addrs: Vec<usize> = (0..8).map(|_| rng.below(8)).collect();
            comp_tables(&addrs, 3, 1).into_iter().next().unwrap()
        })
        .collect();
    let (claims, vclaims) = run_check(&comps, ac, n).unwrap();
    assert_eq!(claims, vclaims);
    for c in &claims {
        let idx: usize = c.poly[1..].parse().unwrap();
        assert_eq!(mle_eval_bits(&comps[idx], &c.point), c.value);
    }
}

#[test]
fn hamming_weight_two_rejected() {
    let (n, ac) = (2usize, 3usize);
    let mut comps = vec![comp_tables(&[1, 2, 3, 4], 3, 1).into_iter().next().unwrap()];
    comps[0][5 + 8 * 2] = true; // second set bit in row j = 2
    assert!(run_check(&comps, ac, n).is_err());
}

#[test]
fn hamming_weight_zero_accepted_here() {
    // The one-hot check alone only proves weight <= 1; weight 0 is
    // caught by the row-sum claim of Shout / Twist.
    let (n, ac) = (2usize, 3usize);
    let mut comps = vec![comp_tables(&[1, 2, 3, 4], 3, 1).into_iter().next().unwrap()];
    for u in 0..8 {
        comps[0][u + 8] = false;
    }
    run_check(&comps, ac, n).unwrap();
}

#[test]
fn virt_d2_d3() {
    let mut rng = Rng(5);
    for (a, d) in [(4usize, 2usize), (6, 3)] {
        let (n, t) = (3usize, 8usize);
        let addrs: Vec<usize> = (0..t).map(|_| rng.below(1 << a)).collect();
        let comps = comp_tables(&addrs, a, d);
        let full = full_table(&comps, a, d, t);
        let r_k = rng.ks(a);
        let (c1, c2) = (rng.ks(n), rng.ks(n));
        let at = |c: &[K]| {
            let mut pt = r_k.clone();
            pt.extend_from_slice(c);
            mle_eval_bits(&full, &pt)
        };
        let (v1, v2) = (at(&c1), at(&c2));
        let names: Vec<String> = (0..d).map(|i| format!("w{i}")).collect();
        let g = VirtGroup {
            names: names.clone(),
            r_k: r_k.clone(),
            terms: vec![
                VirtTerm {
                    cyc: c1.clone(),
                    value: v1,
                },
                VirtTerm {
                    cyc: c2.clone(),
                    value: v2,
                },
            ],
        };
        let (proof, claims) = virt_prove(
            std::slice::from_ref(&g),
            std::slice::from_ref(&comps),
            a,
            d,
            n,
            &mut tr(),
            b"v",
        );
        let vclaims = virt_verify(
            std::slice::from_ref(&g),
            a,
            d,
            n,
            proof.as_ref(),
            &mut tr(),
            b"v",
        )
        .unwrap();
        assert_eq!(claims.len(), d);
        assert_eq!(claims, vclaims);
        for c in &claims {
            let i: usize = c.poly[1..].parse().unwrap();
            assert_eq!(mle_eval_bits(&comps[i], &c.point), c.value);
        }
        let bad = VirtGroup {
            names,
            r_k,
            terms: vec![
                VirtTerm {
                    cyc: c1,
                    value: v1 + K::ONE,
                },
                VirtTerm { cyc: c2, value: v2 },
            ],
        };
        assert!(virt_verify(&[bad], a, d, n, proof.as_ref(), &mut tr(), b"v").is_err());
    }
}
