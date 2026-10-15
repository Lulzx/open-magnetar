//! Port of `reference/tests/test_ring_switch.py`.

mod common;

use common::Rng;
use om_field::K;
use om_pcs::ring_switch::{RingSwitchProof, a_eval, a_table, pack, rs_prove, rs_verify};
use om_sumcheck::{SumcheckProof, eq_table, mle_eval, mle_eval_bits};
use om_transcript::Transcript;

fn setup(ell: usize, seed: u64) -> (Rng, Vec<bool>, Vec<K>, K) {
    let mut rng = Rng(seed);
    let bits = rng.bits(1 << ell);
    let r = rng.ks(ell);
    let y = mle_eval_bits(&bits, &r);
    (rng, bits, r, y)
}

fn fresh() -> Transcript {
    Transcript::new_default(b"t")
}

#[test]
fn pack_matches_convention() {
    let mut bits = vec![false; 256];
    bits[1] = true;
    bits[128 + 127] = true;
    let p = pack(&bits);
    assert_eq!(p[0], K::X);
    assert_eq!(p[1], K::from_u128(1 << 127));
}

#[test]
fn completeness_and_output_claim() {
    for ell in [8usize, 9, 11] {
        let (_rng, bits, r, y) = setup(ell, ell as u64);
        let (proof, r_s, v) = rs_prove(&bits, &r, y, &mut fresh());
        assert_eq!(mle_eval(&pack(&bits), &r_s), v);
        let (r_s2, v2) = rs_verify(&r, y, &proof, &mut fresh()).unwrap();
        assert_eq!((r_s, v), (r_s2, v2));
    }
}

#[test]
fn a_eval_matches_table() {
    let (mut rng, _bits, r, _y) = setup(10, 11);
    let rho = rng.ks(7);
    let z = rng.ks(3);
    assert_eq!(
        a_eval(&r[7..], &rho, &z),
        mle_eval(&a_table(&r[7..], &rho), &z)
    );
}

#[test]
fn wrong_value_rejected() {
    let (_rng, bits, r, y) = setup(10, 11);
    let (proof, ..) = rs_prove(&bits, &r, y, &mut fresh());
    assert!(rs_verify(&r, y + K::ONE, &proof, &mut fresh()).is_err());
}

#[test]
fn tampered_s_rejected_or_output_wrong() {
    // Change s_0 and s_1 so check 1 still holds: either verify rejects or
    // the output claim is false for P.
    let (mut rng, bits, r, y) = setup(10, 11);
    let (proof, ..) = rs_prove(&bits, &r, y, &mut fresh());
    let e = eq_table(&r[..7]);
    let d = rng.k();
    let mut s = proof.s.clone();
    s[0] += d;
    s[1] += d * e[0] / e[1];
    let bad = RingSwitchProof {
        s,
        sumcheck: proof.sumcheck.clone(),
    };
    if let Ok((r_s, v)) = rs_verify(&r, y, &bad, &mut fresh()) {
        assert_ne!(mle_eval(&pack(&bits), &r_s), v);
    }
}

#[test]
fn dishonest_prover_flipped_bit_caught_by_pcs_claim() {
    let (_rng, bits, r, _y) = setup(10, 11);
    let mut bits2 = bits.clone();
    bits2[5] = !bits2[5];
    let y2 = mle_eval_bits(&bits2, &r);
    let (_proof, r_s, v) = rs_prove(&bits2, &r, y2, &mut fresh());
    assert_ne!(mle_eval(&pack(&bits), &r_s), v);
}

#[test]
fn tampered_sumcheck_rejected() {
    let (_rng, bits, r, y) = setup(10, 11);
    let (proof, ..) = rs_prove(&bits, &r, y, &mut fresh());
    let mut msgs = proof.sumcheck.round_msgs.clone();
    msgs[1][0] += K::ONE;
    let bad = RingSwitchProof {
        s: proof.s.clone(),
        sumcheck: SumcheckProof { round_msgs: msgs },
    };
    if let Ok((r2, v2)) = rs_verify(&r, y, &bad, &mut fresh()) {
        assert_ne!(mle_eval(&pack(&bits), &r2), v2);
    }
}

#[test]
fn malformed() {
    let (_rng, bits, r, y) = setup(10, 11);
    let (proof, ..) = rs_prove(&bits, &r, y, &mut fresh());
    let bad = RingSwitchProof {
        s: proof.s[..proof.s.len() - 1].to_vec(),
        sumcheck: proof.sumcheck.clone(),
    };
    assert!(rs_verify(&r, y, &bad, &mut fresh()).is_err());
}
