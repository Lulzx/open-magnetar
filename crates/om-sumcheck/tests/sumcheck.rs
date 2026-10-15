//! Port of `reference/tests/test_sumcheck.py`.

use om_field::K;
use om_sumcheck::{
    SumcheckProof, batch_claims, batched_combine, eq_eval, eq_table, interpolate_eval, mle_eval,
    sumcheck_prove, sumcheck_verify,
};
use om_transcript::Transcript;

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

/// The combine for degree d in the Python tests: product of d tables.
fn combine(d: usize) -> impl Fn(&[K]) -> K {
    move |v: &[K]| v[..d].iter().fold(K::ONE, |a, &x| a * x)
}

fn setup(d: usize, m: usize, seed: u64) -> (Vec<Vec<K>>, K) {
    let mut rng = Rng(seed);
    let tables: Vec<Vec<K>> = (0..d)
        .map(|_| (0..1 << m).map(|_| rng.k()).collect())
        .collect();
    let f = combine(d);
    let mut claim = K::ZERO;
    for i in 0..1 << m {
        let vals: Vec<K> = tables.iter().map(|t| t[i]).collect();
        claim += f(&vals);
    }
    (tables, claim)
}

struct Pv {
    tables: Vec<Vec<K>>,
    proof: SumcheckProof,
    rs: Vec<K>,
    evals: Vec<K>,
    r: Vec<K>,
    exp: K,
}

fn run_pv(d: usize, m: usize, seed: u64) -> Pv {
    let (tables, claim) = setup(d, m, seed);
    let f = combine(d);
    let mut pt = Transcript::new_default(b"om/sc");
    let (proof, rs, evals) = sumcheck_prove(claim, tables.clone(), &f, d, &mut pt, b"sc/round");
    let mut vt = Transcript::new_default(b"om/sc");
    let (r, exp) = sumcheck_verify(claim, m, d, &proof, &mut vt, b"sc/round").unwrap();
    Pv {
        tables,
        proof,
        rs,
        evals,
        r,
        exp,
    }
}

#[test]
fn test_completeness() {
    for d in [1, 2, 3] {
        for m in [0, 1, 2, 5] {
            let pv = run_pv(d, m, 1);
            assert_eq!(pv.r, pv.rs, "d={d} m={m}");
            assert_eq!(pv.exp, combine(d)(&pv.evals), "d={d} m={m}");
            let direct: Vec<K> = pv.tables.iter().map(|t| mle_eval(t, &pv.r)).collect();
            assert_eq!(pv.evals, direct, "d={d} m={m}");
            assert!(
                pv.proof.round_msgs.iter().all(|x| x.len() == d),
                "d={d} m={m}"
            );
            assert_eq!(pv.proof.round_msgs.len(), m, "d={d} m={m}");
        }
    }
}

#[test]
fn test_bit_tables() {
    let mut rng = Rng(9);
    let bits: Vec<bool> = (0..16).map(|_| rng.bit()).collect();
    // Python passes the 0/1 int table directly; Rust callers convert.
    let t: Vec<K> = bits.iter().map(|&b| K::from_bit(b)).collect();
    let f = |v: &[K]| v[0] * v[0];
    let claim = t.iter().fold(K::ZERO, |a, &x| a + x);
    let (proof, _rs, ev) = sumcheck_prove(
        claim,
        vec![t],
        &f,
        2,
        &mut Transcript::new_default(b"x"),
        b"s",
    );
    let (_r, exp) = sumcheck_verify(
        claim,
        4,
        2,
        &proof,
        &mut Transcript::new_default(b"x"),
        b"s",
    )
    .unwrap();
    assert_eq!(exp, f(&ev));
}

#[test]
fn test_tampered_message() {
    let pv = run_pv(2, 4, 1);
    let (_tables, claim) = setup(2, 4, 1);
    let mut bad = pv.proof.clone();
    bad.round_msgs[1][0] += K::ONE;
    let (_r2, exp2) = sumcheck_verify(
        claim,
        4,
        2,
        &bad,
        &mut Transcript::new_default(b"om/sc"),
        b"sc/round",
    )
    .unwrap();
    assert_ne!(exp2, combine(2)(&pv.evals));

    let truncated = SumcheckProof {
        round_msgs: pv.proof.round_msgs[..3].to_vec(),
    };
    let err = sumcheck_verify(
        claim,
        4,
        2,
        &truncated,
        &mut Transcript::new_default(b"om/sc"),
        b"sc/round",
    )
    .unwrap_err();
    assert_eq!(err.message(), "wrong number of rounds");

    let mut short = pv.proof.clone();
    short.round_msgs[0].pop();
    let err = sumcheck_verify(
        claim,
        4,
        2,
        &short,
        &mut Transcript::new_default(b"om/sc"),
        b"sc/round",
    )
    .unwrap_err();
    assert_eq!(err.message(), "malformed round message");
    // VerificationError is a proper std error.
    let _: &dyn std::error::Error = &err;
    assert_eq!(err.to_string(), "malformed round message");
}

#[test]
#[should_panic(expected = "claim inconsistent with tables")]
fn test_wrong_claim_prove_panics() {
    let (tables, claim) = setup(3, 4, 2);
    let _ = sumcheck_prove(
        claim + K::ONE,
        tables,
        &combine(3),
        3,
        &mut Transcript::new_default(b"om/sc"),
        b"s",
    );
}

#[test]
fn test_wrong_claim_verify_mismatch() {
    let (tables, claim) = setup(3, 4, 2);
    let (proof, _rs, evals) = sumcheck_prove(
        claim,
        tables,
        &combine(3),
        3,
        &mut Transcript::new_default(b"om/sc"),
        b"s",
    );
    let (_r, exp) = sumcheck_verify(
        claim + K::ONE,
        4,
        3,
        &proof,
        &mut Transcript::new_default(b"om/sc"),
        b"s",
    )
    .unwrap();
    assert_ne!(exp, combine(3)(&evals));
}

#[test]
fn test_interpolate() {
    let mut rng = Rng(7);
    let c: Vec<K> = (0..4).map(|_| rng.k()).collect();
    let p = |x: K| c[0] + c[1] * x + c[2] * x * x + c[3] * x * x * x;
    let ys: Vec<K> = (0..4).map(|k| p(K::t(k))).collect();
    let z = rng.k();
    assert_eq!(interpolate_eval(&ys, z), p(z));
    // Evaluating at the nodes recovers the values.
    for k in 0..4 {
        assert_eq!(interpolate_eval(&ys, K::t(k)), ys[k as usize]);
    }
}

#[test]
fn test_eq_sumcheck() {
    // sum_b eq(tau,b) * a(b) * b(b) == claim; degree 3.
    let mut rng = Rng(11);
    let m = 4;
    let tau: Vec<K> = (0..m).map(|_| rng.k()).collect();
    let a: Vec<K> = (0..1 << m).map(|_| K::from_bit(rng.bit())).collect();
    let b: Vec<K> = (0..1 << m).map(|_| K::from_bit(rng.bit())).collect();
    let e = eq_table(&tau);
    let f = combine(3);
    let mut claim = K::ZERO;
    for i in 0..1 << m {
        claim += f(&[e[i], a[i], b[i]]);
    }
    let (proof, rs, ev) = sumcheck_prove(
        claim,
        vec![e, a, b],
        &f,
        3,
        &mut Transcript::new_default(b"x"),
        b"s",
    );
    let (_r, exp) = sumcheck_verify(
        claim,
        m,
        3,
        &proof,
        &mut Transcript::new_default(b"x"),
        b"s",
    )
    .unwrap();
    assert_eq!(exp, f(&ev));
    assert_eq!(ev[0], eq_eval(&tau, &rs));
}

#[test]
fn test_batching() {
    let m = 3;
    let (t1, c1) = setup(2, m, 21);
    let (t2, c2) = setup(3, m, 22);
    let mut pt = Transcript::new_default(b"x");
    let (coeffs, comb) = batch_claims(&[c1, c2], &mut pt, b"b");
    assert_eq!(coeffs[0], K::ONE);
    let f = batched_combine(
        coeffs.clone(),
        vec![Box::new(combine(2)), Box::new(combine(3))],
        vec![2, 3],
    );
    let tables: Vec<Vec<K>> = t1.into_iter().chain(t2).collect();
    let (proof, _rs, ev) = sumcheck_prove(comb, tables, &*f, 3, &mut pt, b"s");
    let mut vt = Transcript::new_default(b"x");
    let (coeffs_v, comb_v) = batch_claims(&[c1, c2], &mut vt, b"b");
    assert_eq!(comb, comb_v);
    assert_eq!(coeffs, coeffs_v);
    let (_r, exp) = sumcheck_verify(comb_v, m, 3, &proof, &mut vt, b"s").unwrap();
    let fv = batched_combine(
        coeffs_v,
        vec![Box::new(combine(2)), Box::new(combine(3))],
        vec![2, 3],
    );
    assert_eq!(exp, fv(&ev));
}

#[test]
fn test_batch_claims_256_ok_and_coeffs_are_powers() {
    let claims: Vec<K> = (0..256u128).map(K::from_u128).collect();
    let mut t = Transcript::new_default(b"x");
    let (coeffs, combined) = batch_claims(&claims, &mut t, b"b");
    assert_eq!(coeffs.len(), 256);
    assert_eq!(coeffs[0], K::ONE);
    // Coeffs are successive powers of one gamma.
    let gamma = coeffs[1];
    for i in 2..256 {
        assert_eq!(coeffs[i], coeffs[i - 1] * gamma);
    }
    let expect = claims
        .iter()
        .zip(&coeffs)
        .fold(K::ZERO, |a, (&x, &c)| a + c * x);
    assert_eq!(combined, expect);
    // Empty batch: no coeffs, combined zero (Python behaviour).
    let (coeffs, combined) = batch_claims(&[], &mut Transcript::new_default(b"x"), b"b");
    assert!(coeffs.is_empty());
    assert_eq!(combined, K::ZERO);
}

#[test]
#[should_panic(expected = "limited to 256 claims")]
fn test_batch_claims_257_rejected() {
    let claims = vec![K::ONE; 257];
    let mut t = Transcript::new_default(b"x");
    let _ = batch_claims(&claims, &mut t, b"b");
}

#[test]
#[should_panic(expected = "degree must be >= 1")]
fn test_prove_degree_zero_panics() {
    let _ = sumcheck_prove(
        K::ZERO,
        vec![vec![K::ONE]],
        &combine(1),
        0,
        &mut Transcript::new_default(b"x"),
        b"s",
    );
}

#[test]
#[should_panic(expected = "degree must be >= 1")]
fn test_verify_degree_zero_panics() {
    let proof = SumcheckProof { round_msgs: vec![] };
    let _ = sumcheck_verify(
        K::ZERO,
        0,
        0,
        &proof,
        &mut Transcript::new_default(b"x"),
        b"s",
    );
}
