//! Port of `reference/tests/test_ligerito.py` (the two monkeypatching
//! cheating-prover tests live as unit tests in `src/ligerito.rs`, where
//! they can use the internal commit hook).

mod common;

use common::Rng;
use om_field::K;
use om_pcs::ligerito::{self as lg, LigeritoParams, LigeritoProof};
use om_pcs::ring_switch as rsw;
use om_pcs::{BitPCS, Commitment, LigeritoPCS, Pcs};
use om_sumcheck::{mle_eval, mle_eval_bits};
use om_transcript::{Hasher, Transcript};

fn run(
    p: &LigeritoParams,
    seed: u64,
) -> (LigeritoPCS, Vec<K>, Commitment, Vec<K>, K, LigeritoProof) {
    let mut rng = Rng(seed);
    let pcs = LigeritoPCS::new(p.clone());
    let tab = rng.ks(1 << p.n);
    let mut tr = Transcript::new_default(b"t");
    let (cm, st) = Pcs::commit(&pcs, &tab, &mut tr);
    let r = rng.ks(p.n);
    let (y, pf) = Pcs::open(&pcs, &st, &r, &mut tr);
    (pcs, tab, cm, r, y, pf)
}

fn check(
    pcs: &LigeritoPCS,
    cm: &Commitment,
    r: &[K],
    y: K,
    pf: &LigeritoProof,
) -> Result<(), om_sumcheck::VerificationError> {
    let mut tv = Transcript::new_default(b"t");
    Pcs::absorb_commitment(pcs, cm, &mut tv);
    Pcs::verify(pcs, cm, r, y, pf, &mut tv)
}

fn p_default() -> LigeritoParams {
    LigeritoParams::new(10, vec![3, 3], vec![1, 2], vec![6, 5])
}

#[test]
fn completeness() {
    for p in [
        LigeritoParams::new(8, vec![3], vec![1], vec![5]),
        p_default(),
        LigeritoParams::new(9, vec![2, 2, 2], vec![2, 1, 2], vec![4, 4, 4]),
    ] {
        let (pcs, tab, cm, r, y, pf) = run(&p, 1);
        assert_eq!(y, mle_eval(&tab, &r));
        check(&pcs, &cm, &r, y, &pf).unwrap();
    }
}

#[test]
fn wrong_value() {
    let (pcs, _t, cm, r, y, pf) = run(&p_default(), 1);
    assert!(check(&pcs, &cm, &r, y + K::ONE, &pf).is_err());
}

#[test]
fn wrong_point() {
    let (pcs, _t, cm, mut r, y, pf) = run(&p_default(), 1);
    r[0] += K::ONE;
    assert!(check(&pcs, &cm, &r, y, &pf).is_err());
}

#[test]
fn tamper_everything() {
    let (pcs, _t, cm, r, y, pf) = run(&p_default(), 1);
    let mut cases: Vec<LigeritoProof> = Vec::new();
    // sumcheck message
    let mut c = pf.clone();
    c.sumchecks[0].round_msgs[0][0] += K::ONE;
    cases.push(c);
    // opened column value
    let mut c = pf.clone();
    c.openings[0].columns[0][0] += K::ONE;
    cases.push(c);
    // Merkle auth path
    let mut c = pf.clone();
    c.openings[1].auth[0][0] ^= 1;
    cases.push(c);
    // next-level root
    let mut c = pf.clone();
    c.roots[0][0] ^= 1;
    cases.push(c);
    // final polynomial
    let mut c = pf.clone();
    c.final_poly[0] += K::ONE;
    cases.push(c);
    for (i, c) in cases.iter().enumerate() {
        assert!(check(&pcs, &cm, &r, y, c).is_err(), "case {i}");
    }
}

#[test]
fn wrong_commitment() {
    let (pcs, _t, cm, r, y, pf) = run(&p_default(), 1);
    let cm2 = Commitment {
        root: vec![0u8; 32],
        n: cm.n,
    };
    assert!(check(&pcs, &cm2, &r, y, &pf).is_err());
}

#[test]
fn params_and_queries() {
    assert_eq!(lg::queries_provable(2, 120), 177);
    assert_eq!(lg::queries_provable(1, 120), 290);
    assert_eq!(lg::queries_conjectured(2, 100), 50);
    assert_eq!(lg::schedule(24), vec![5, 5, 4, 4]);
    assert_eq!(lg::schedule(20), vec![5, 5, 4]);
    assert_eq!(lg::schedule(22), vec![4, 4, 4, 4]);
    for r in 2..=8 {
        for d in lg::soundness_bits(&lg::make_params(24, "provable-120", r), "provable-120") {
            assert!(d.query >= 120.0, "{d:?}");
            assert!(d.sumcheck >= 120.0, "{d:?}");
            assert!(d.batch >= 120.0, "{d:?}");
            assert!(d.gap >= 120.0, "{d:?}");
        }
    }
    // r = 1 gives t = 290 > 256 (batching bits 119.82 < 120), so provable-120 must reject it.
    assert!(std::panic::catch_unwind(|| lg::make_params(24, "provable-120", 1)).is_err());
    assert!(std::panic::catch_unwind(|| lg::make_params(24, "provable-120", 9)).is_err());
}

#[test]
fn bitpcs_packed_matches_bool() {
    let ell = 11usize; // packed n = 4
    let p = LigeritoParams::new(ell - 7, vec![2], vec![1], vec![6]);
    let mut rng = Rng(3);
    let bits = rng.bits(1 << ell);
    let packed = om_sumcheck::PackedBits::from_bools(&bits);
    let b = BitPCS::new(p.clone());

    let mut tr1 = Transcript::new_default(b"t");
    let (cm1, st1) = b.commit(&bits, &mut tr1);
    let r = rng.ks(ell);
    let (y1, pf1) = b.open(&st1, &r, &mut tr1);

    let mut tr2 = Transcript::new_default(b"t");
    let (cm2, st2) = b.commit_packed(&packed, &mut tr2);
    let (y2, pf2) = b.open_packed(st2, &packed, &r, &mut tr2);

    assert_eq!((&cm1, y1, &pf1), (&cm2, y2, &pf2));
    let mut tv = Transcript::new_default(b"t");
    b.pcs.absorb_commitment(&cm2, &mut tv);
    b.verify(&cm2, &r, y2, &pf2, &mut tv).unwrap();
}

#[test]
fn bitpcs_end_to_end_and_negative() {
    let ell = 11usize; // packed n = 4
    let p = LigeritoParams::new(ell - 7, vec![2], vec![1], vec![6]);
    let mut rng = Rng(3);
    let bits = rng.bits(1 << ell);
    let b = BitPCS::new(p.clone());
    let mut tr = Transcript::new_default(b"t");
    let (cm, st) = b.commit(&bits, &mut tr);
    let r = rng.ks(ell);
    let (y, pf) = b.open(&st, &r, &mut tr);
    assert_eq!(y, mle_eval_bits(&bits, &r));

    let mut tv = Transcript::new_default(b"t");
    b.pcs.absorb_commitment(&cm, &mut tv);
    b.verify(&cm, &r, y, &pf, &mut tv).unwrap();

    let mut tv = Transcript::new_default(b"t");
    b.pcs.absorb_commitment(&cm, &mut tv);
    assert!(b.verify(&cm, &r, y + K::ONE, &pf, &mut tv).is_err());

    // A prover opening a different bit vector against this commitment.
    let mut bits2 = bits.clone();
    bits2[9] = !bits2[9];
    let y2 = mle_eval_bits(&bits2, &r);
    let mut tr = Transcript::new_default(b"t");
    b.pcs.absorb_commitment(&cm, &mut tr);
    let (rs_proof, r_s, _v) = rsw::rs_prove(&bits2, &r, y2, &mut tr);
    let yp = mle_eval(&st.0.f, &r_s);
    let pf2 = lg::open_(&p, b.pcs.h, &st.0, &r_s, yp, &mut tr);
    let mut tv = Transcript::new_default(b"t");
    b.pcs.absorb_commitment(&cm, &mut tv);
    assert!(b.verify(&cm, &r, y2, &(rs_proof, pf2), &mut tv).is_err());
}

// ------------------------------------------------------------- gap (4.4a)

fn p2() -> LigeritoParams {
    LigeritoParams::with_gs(10, vec![3, 3], vec![1, 2], vec![30, 30], vec![2, 2])
}
fn p3() -> LigeritoParams {
    LigeritoParams::with_gs(9, vec![2, 2], vec![2, 2], vec![12, 12], vec![3, 1])
}

#[test]
fn gap_completeness() {
    for p in [
        p2(),
        p3(),
        LigeritoParams::with_gs(8, vec![3], vec![1], vec![5], vec![2]),
    ] {
        let (pcs, tab, cm, r, y, pf) = run(&p, 1);
        assert_eq!(y, mle_eval(&tab, &r));
        check(&pcs, &cm, &r, y, &pf).unwrap();
        assert_eq!(pf.final_poly.len(), 1 << p.n_final());
    }
}

#[test]
fn gap_wrong_value() {
    let (pcs, _t, cm, r, y, pf) = run(&p2(), 1);
    assert!(check(&pcs, &cm, &r, y + K::ONE, &pf).is_err());
}

#[test]
fn gap_tamper_each_repetition_in_final() {
    for p in [p2(), p3()] {
        let (pcs, _t, cm, r, y, pf) = run(&p, 1);
        let m = p.m_i(p.levels() - 1);
        for j in 0..p.reps(p.levels() - 1) {
            let mut c = pf.clone();
            c.final_poly[j << m] += K::ONE;
            assert!(check(&pcs, &cm, &r, y, &c).is_err(), "block {j}");
        }
    }
}

#[test]
fn gap_params_encoding_and_shape() {
    assert_eq!(p2().n_i(1), 10 - 3 + 1);
    assert_eq!(p2().n_final(), 10 - 6 + 2);
    assert_eq!(p3().sbits(0), 2);
    assert_eq!(p3().sbits(1), 0);
    // GAPREPS suffix only when some gs_i > 1.
    assert!(p2().encode().windows(7).any(|w| w == b"GAPREPS"));
    assert!(!p_default().encode().windows(7).any(|w| w == b"GAPREPS"));
    assert_eq!(p_default().encode().len(), 8 * (2 + 3 * 2));
    assert_eq!(p2().encode().len(), 8 * (2 + 3 * 2) + 7 + 8 * 2);
}

// ---------------------------------------------------------- provable-120

#[test]
fn provable120_profile_end_to_end() {
    let p = lg::make_params(8, "provable-120", 2);
    assert_eq!(p.ts, vec![177]);
    assert_eq!(p.gs, vec![2]);
    assert_eq!(p.ks, vec![2]);
    for d in lg::soundness_bits(&p, "provable-120") {
        assert!(
            d.gap.min(d.query).min(d.sumcheck).min(d.batch) >= 120.0,
            "{d:?}"
        );
    }
    let (pcs, tab, cm, r, y, pf) = run(&p, 1);
    assert_eq!(y, mle_eval(&tab, &r));
    check(&pcs, &cm, &r, y, &pf).unwrap();
    assert!(check(&pcs, &cm, &r, y + K::ONE, &pf).is_err());
}

#[test]
fn provable120_two_levels_bitpcs() {
    let ell = 7 + 12;
    let p = lg::make_params(ell - 7, "provable-120", 2);
    assert_eq!(p.ks.len(), 2);
    assert!(p.gs.iter().all(|&g| g == 2));
    let mut rng = Rng(4);
    let bits = rng.bits(1 << ell);
    let b = BitPCS::new(p);
    let mut tr = Transcript::new_default(b"t");
    let (cm, st) = b.commit(&bits, &mut tr);
    let r = rng.ks(ell);
    let (y, pf) = b.open(&st, &r, &mut tr);
    let mut tv = Transcript::new_default(b"t");
    b.pcs.absorb_commitment(&cm, &mut tv);
    b.verify(&cm, &r, y, &pf, &mut tv).unwrap();
    let mut tv = Transcript::new_default(b"t");
    b.pcs.absorb_commitment(&cm, &mut tv);
    assert!(b.verify(&cm, &r, y + K::ONE, &pf, &mut tv).is_err());
}

#[test]
fn conjectured100_profile_shape() {
    let p = lg::make_params(20, "conjectured-100", 2);
    assert!(p.ts.iter().all(|&t| t == 50));
    assert!(p.gs.is_empty());
    let _ = Hasher::Sha256; // profile hashes are orthogonal to params
}

#[test]
fn bitpcs_packed_matches_bool_multilevel() {
    // Several levels, both profiles (provable-120 has gs = 2, so the
    // second fold reads the level table after its sum-check), and
    // enough variables that the split eq tables of ring switching are
    // non-trivial. The packed path keeps only the tree after commit
    // and re-encodes the queried columns.
    for (ell, profile) in [
        (19usize, "provable-120"),
        (20, "conjectured-100"),
        (14, "conjectured-100"),
    ] {
        let p = lg::make_params(ell - 7, profile, 2);
        let mut rng = Rng(ell as u64);
        let bits = rng.bits(1 << ell);
        let packed = om_sumcheck::PackedBits::from_bools(&bits);
        let b = BitPCS::new(p.clone());
        let r = rng.ks(ell);

        let mut tr1 = Transcript::new_default(b"t");
        let (cm1, st1) = b.commit(&bits, &mut tr1);
        let (y1, pf1) = b.open(&st1, &r, &mut tr1);

        let mut tr2 = Transcript::new_default(b"t");
        let (cm2, st2) = b.commit_packed(&packed, &mut tr2);
        assert!(st2.f.is_empty() && st2.cw.is_empty());
        let (y2, pf2) = b.open_packed(st2, &packed, &r, &mut tr2);

        assert_eq!((&cm1, y1, &pf1), (&cm2, y2, &pf2), "ell {ell} {profile}");
        assert_eq!(y1, mle_eval_bits(&bits, &r));
        let mut tv = Transcript::new_default(b"t");
        b.pcs.absorb_commitment(&cm2, &mut tv);
        b.verify(&cm2, &r, y2, &pf2, &mut tv).unwrap();
    }
}
