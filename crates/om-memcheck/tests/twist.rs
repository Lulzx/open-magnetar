//! Port of `reference/tests/test_twist.py`.

mod common;

use common::Rng;
use om_field::K;
use om_memcheck::onehot::bits_of;
use om_memcheck::twist::{
    FinalMem, TwistClaims, TwistInfo, TwistParams, TwistProof, TwistWitness, build_witness,
    honest_claims, lt_eval, lt_table, m0_table, twist_prove, twist_verify,
};
use om_sumcheck::mle_eval_bits;
use om_transcript::Transcript;

fn tr() -> Transcript {
    Transcript::new_default(b"test/twist")
}

struct Setup {
    params: TwistParams,
    m0: Vec<u64>,
    wit: TwistWitness,
    info: TwistInfo,
    claims: TwistClaims,
    m0t: Vec<bool>,
}

fn setup(a: usize, d: usize, p: usize, n: usize, ell: usize, seed: u64) -> Setup {
    setup_hot(a, d, p, n, ell, seed, false)
}

fn setup_hot(a: usize, d: usize, p: usize, n: usize, ell: usize, seed: u64, hot: bool) -> Setup {
    let mut rng = Rng(seed);
    let (nk, t, l) = (1usize << a, 1usize << n, 1u32 << ell);
    let mut m0: Vec<u64> = (0..nk)
        .map(|_| if rng.bit() { rng.word(l) } else { 0 })
        .collect();
    if hot {
        m0[0] = 0;
    }
    let reads: Vec<Vec<usize>> = (0..p)
        .map(|_| (0..t).map(|_| rng.below(nk)).collect())
        .collect();
    let writes: Vec<usize> = (0..t).map(|_| rng.below(nk)).collect();
    let new: Vec<u64> = (0..t).map(|_| rng.word(l)).collect();
    let params = TwistParams {
        name: "tw".to_string(),
        a,
        d,
        p,
        n,
        ell,
    };
    let (wit, info) = build_witness(&params, &m0, &reads, &writes, &new);
    let r_o = rng.ks(ell);
    let r_c = rng.ks(n);
    let claims = honest_claims(&params, &info, &r_o, &r_c);
    let m0t = m0_table(&m0, a, ell);
    Setup {
        params,
        m0,
        wit,
        info,
        claims,
        m0t,
    }
}

fn final_spec(info: &TwistInfo, m: usize, s_out: usize) -> FinalMem {
    let base = s_out << m;
    FinalMem {
        m,
        s_out,
        words: (0..1 << m).map(|i| info.final_state[base + i]).collect(),
    }
}

fn verify(
    s: &Setup,
    claims: &TwistClaims,
    proof: &TwistProof,
    fin: Option<&FinalMem>,
    inc_extra: bool,
) -> Result<om_memcheck::twist::TwistOutput, om_sumcheck::VerificationError> {
    twist_verify(
        &s.params,
        &|pt: &[K]| mle_eval_bits(&s.m0t, pt),
        claims,
        proof,
        &mut tr(),
        b"T",
        fin,
        inc_extra,
    )
}

#[test]
fn lt_brute_force() {
    let n = 4;
    for x in 0..16u64 {
        for y in 0..16u64 {
            assert_eq!(lt_eval(&bits_of(x, n), &bits_of(y, n)), K::from_bit(x < y));
        }
    }
}

#[test]
fn lt_is_mle() {
    let mut rng = Rng(1);
    let n = 3;
    let y = rng.ks(n);
    let t = lt_table(&y);
    let x = rng.ks(n);
    assert_eq!(lt_eval(&x, &y), om_sumcheck::mle_eval(&t, &x));
}

#[allow(clippy::too_many_arguments)]
fn run_case(
    a: usize,
    d: usize,
    p: usize,
    n: usize,
    ell: usize,
    seed: u64,
    fin: Option<(usize, usize)>,
    inc_extra: bool,
) -> (Setup, Option<FinalMem>, TwistProof) {
    let s = setup(a, d, p, n, ell, seed);
    let fin = fin.map(|(m, s_out)| final_spec(&s.info, m, s_out));
    let (proof, out) = twist_prove(
        &s.params,
        &s.m0,
        &s.wit,
        &s.claims,
        &mut tr(),
        b"T",
        fin.as_ref(),
        inc_extra,
    );
    let vout = verify(&s, &s.claims, &proof, fin.as_ref(), inc_extra).unwrap();
    assert_eq!(out.claims, vout.claims);
    assert_eq!(out.inc_extra, vout.inc_extra);
    // Every output claim is a true evaluation of a committed polynomial.
    for x in &vout.claims {
        if x.poly.ends_with("/inc") {
            assert_eq!(mle_eval_bits(&s.wit.inc, &x.point), x.value, "{}", x.poly);
        } else {
            let parts: Vec<&str> = x.poly.split('/').collect();
            let (kind, i) = (parts[1], parts[2].parse::<usize>().unwrap() - 1);
            let comp = if kind == "wa" {
                &s.wit.wa[i]
            } else {
                &s.wit.ra[kind[2..].parse::<usize>().unwrap()][i]
            };
            assert_eq!(mle_eval_bits(comp, &x.point), x.value, "{}", x.poly);
        }
    }
    (s, fin, proof)
}

#[test]
fn reg_like_p2_d1() {
    run_case(3, 1, 2, 3, 6, 11, None, false);
}

#[test]
fn reg_like_p2_d2() {
    run_case(4, 2, 2, 3, 6, 12, None, true);
}

#[test]
fn ram_like_p1_d1() {
    run_case(3, 1, 1, 3, 6, 13, Some((2, 1)), true);
}

#[test]
fn ram_like_p1_d2_final() {
    run_case(4, 2, 1, 3, 6, 14, Some((2, 3)), true);
}

#[test]
fn twist_d3() {
    run_case(6, 3, 1, 2, 4, 15, Some((3, 5)), false);
}

#[test]
fn real_register_shape() {
    // 64 registers, p = 2, d = 2 (default), L = 64.
    run_case(6, 2, 2, 3, 6, 16, None, false);
}

#[test]
fn ram_shared_write_address() {
    // RAM instance: wa components are the ra components (reads == writes).
    let mut rng = Rng(50);
    let (a, d, n) = (4usize, 2usize, 3usize);
    let m0: Vec<u64> = (0..16).map(|_| rng.word(64)).collect();
    let addrs: Vec<usize> = (0..8).map(|_| rng.below(16)).collect();
    let new: Vec<u64> = (0..8).map(|_| rng.word(64)).collect();
    let params = TwistParams {
        name: "tw".to_string(),
        a,
        d,
        p: 1,
        n,
        ell: 6,
    };
    let (wit, info) = build_witness(&params, &m0, std::slice::from_ref(&addrs), &addrs, &new);
    assert_eq!(wit.ra[0], wit.wa);
    let claims = honest_claims(&params, &info, &rng.ks(6), &rng.ks(n));
    assert_eq!(claims.bits[0], claims.bits[1]);
    let m0t = m0_table(&m0, a, 6);
    let (proof, _) = twist_prove(&params, &m0, &wit, &claims, &mut tr(), b"T", None, false);
    twist_verify(
        &params,
        &|pt: &[K]| mle_eval_bits(&m0t, pt),
        &claims,
        &proof,
        &mut tr(),
        b"T",
        None,
        false,
    )
    .unwrap();
}

#[test]
fn wrong_read_value() {
    let (s, _fin, proof) = run_case(4, 2, 2, 3, 6, 21, None, false);
    let mut rv = s.claims.rv.clone();
    rv[1] += K::ONE;
    let bad = TwistClaims {
        rv,
        ..s.claims.clone()
    };
    assert!(verify(&s, &bad, &proof, None, false).is_err());
}

#[test]
fn wrong_read_trace() {
    // Prover's read value table differs from the memory: claims built
    // from a corrupted rv, proof built honestly.
    let s = setup(4, 2, 2, 3, 6, 22);
    let mut info2 = s.info.clone();
    info2.rv[0][3] ^= 1 << 17;
    let bad = honest_claims(&s.params, &info2, &s.claims.r_o, &s.claims.r_c);
    let (proof, _) = twist_prove(&s.params, &s.m0, &s.wit, &bad, &mut tr(), b"T", None, false);
    assert!(verify(&s, &bad, &proof, None, false).is_err());
}

#[test]
fn wrong_write_value() {
    let s = setup(3, 1, 1, 3, 6, 23);
    let bad = TwistClaims {
        wv: s.claims.wv + K::ONE,
        ..s.claims.clone()
    };
    let (proof, _) = twist_prove(&s.params, &s.m0, &s.wit, &bad, &mut tr(), b"T", None, false);
    assert!(verify(&s, &bad, &proof, None, false).is_err());
}

#[test]
fn wrong_address_bit() {
    let s = setup(4, 2, 1, 3, 6, 24);
    let mut bits = s.claims.bits.clone();
    bits[0][1] += K::ONE;
    let bad = TwistClaims {
        bits,
        ..s.claims.clone()
    };
    let (proof, _) = twist_prove(&s.params, &s.m0, &s.wit, &bad, &mut tr(), b"T", None, false);
    assert!(verify(&s, &bad, &proof, None, false).is_err());
}

#[test]
fn hamming_two_read() {
    let mut s = setup(4, 2, 2, 3, 6, 25);
    s.wit.ra[1][0][1 + 4 * 2] = true;
    s.wit.ra[1][0][2 + 4 * 2] = true;
    let (proof, _) = twist_prove(
        &s.params,
        &s.m0,
        &s.wit,
        &s.claims,
        &mut tr(),
        b"T",
        None,
        false,
    );
    assert!(verify(&s, &s.claims, &proof, None, false).is_err());
}

#[test]
fn hamming_zero_write() {
    for d in [1usize, 2] {
        let mut s = setup(4, d, 1, 3, 6, 26);
        let ac = 4 / d;
        for u in 0..1 << ac {
            s.wit.wa[0][u + (1 << ac) * 4] = false;
        }
        let (proof, _) = twist_prove(
            &s.params,
            &s.m0,
            &s.wit,
            &s.claims,
            &mut tr(),
            b"T",
            None,
            false,
        );
        assert!(verify(&s, &s.claims, &proof, None, false).is_err());
    }
}

#[test]
fn hamming_zero_read() {
    let mut s = setup(4, 2, 1, 3, 6, 27);
    for u in 0..4 {
        s.wit.ra[0][1][u + 4 * 6] = false;
    }
    let (proof, _) = twist_prove(
        &s.params,
        &s.m0,
        &s.wit,
        &s.claims,
        &mut tr(),
        b"T",
        None,
        false,
    );
    assert!(verify(&s, &s.claims, &proof, None, false).is_err());
}

#[test]
fn wrong_increment() {
    // Increment table inconsistent with the claimed written value.
    let mut s = setup(3, 1, 1, 3, 6, 28);
    s.wit.inc[5 + 64 * 2] ^= true;
    let (proof, _) = twist_prove(
        &s.params,
        &s.m0,
        &s.wit,
        &s.claims,
        &mut tr(),
        b"T",
        None,
        false,
    );
    assert!(verify(&s, &s.claims, &proof, None, false).is_err());
}

#[test]
fn wrong_final_memory() {
    let (s, fin, proof) = run_case(4, 2, 1, 3, 6, 29, Some((2, 1)), false);
    let mut fin = fin.unwrap();
    fin.words[2] ^= 1 << 40;
    assert!(verify(&s, &s.claims, &proof, Some(&fin), false).is_err());
}

#[test]
fn wrong_final_region() {
    let (s, _fin, proof) = run_case(4, 1, 1, 3, 6, 30, Some((2, 1)), false);
    let other = final_spec(&s.info, 2, 2);
    assert!(verify(&s, &s.claims, &proof, Some(&other), false).is_err());
}

#[test]
fn final_untouched_region_equals_m0() {
    // A region never written: final memory equals M0 there.
    let (a, d, p, n, ell) = (4usize, 1usize, 1usize, 2usize, 6usize);
    let mut rng = Rng(40);
    let m0: Vec<u64> = (0..16).map(|_| rng.word(64)).collect();
    let reads: Vec<Vec<usize>> = vec![(0..4).map(|_| rng.below(8)).collect()];
    let writes: Vec<usize> = (0..4).map(|_| rng.below(8)).collect();
    let new: Vec<u64> = (0..4).map(|_| rng.word(64)).collect();
    let params = TwistParams {
        name: "tw".to_string(),
        a,
        d,
        p,
        n,
        ell,
    };
    let (wit, info) = build_witness(&params, &m0, &reads, &writes, &new);
    let claims = honest_claims(&params, &info, &rng.ks(6), &rng.ks(2));
    let fin = FinalMem {
        m: 3,
        s_out: 1,
        words: m0[8..16].to_vec(),
    };
    let m0t = m0_table(&m0, a, ell);
    let (proof, _) = twist_prove(
        &params,
        &m0,
        &wit,
        &claims,
        &mut tr(),
        b"T",
        Some(&fin),
        false,
    );
    twist_verify(
        &params,
        &|pt: &[K]| mle_eval_bits(&m0t, pt),
        &claims,
        &proof,
        &mut tr(),
        b"T",
        Some(&fin),
        false,
    )
    .unwrap();
}
