//! Port of `reference/tests/test_spartan.py` (TestR1CS,
//! TestSingleSpartan, TestVirtualSpartan). Python's `ValueError` on the
//! prover side maps to a panic; `VerificationError` maps to `Err`.

mod common;

use common::Rng;
use om_field::K;
use om_spartan::r1cs::{R1CS, RelationField, SparseMatrix, flatten_w, simd_satisfied};
use om_spartan::spartan::{
    CrossStep, Segment, SegmentKind, SpartanProof, check_layout, next_mle, prove, segment_table,
    verify,
};
use om_sumcheck::{mle_eval, mle_eval_bits};
use om_transcript::Transcript;

fn fresh() -> Transcript {
    Transcript::new_default(b"test")
}

fn rng() -> Rng {
    Rng(2024)
}

// ---------------------------------------------------------------- TestR1CS

#[test]
fn mle_matches_bruteforce() {
    let mut r = rng();
    let m = SparseMatrix::new(
        2,
        3,
        [
            ((0, 1), K::from_u128(5)),
            ((3, 7), K::from_u128(9)),
            ((2, 2), K::ONE),
        ],
    );
    let rr = r.ks(2);
    let rc = r.ks(3);
    let mut dense = vec![K::ZERO; 32];
    for &(row, col, v) in m.entries() {
        dense[row + 4 * col] = v;
    }
    let mut point = rr.clone();
    point.extend_from_slice(&rc);
    assert_eq!(m.mle(&rr, &rc), mle_eval(&dense, &point));
    let ft = m.fold_rows(&rr);
    assert_eq!(mle_eval(&ft, &rc), m.mle(&rr, &rc));
}

#[test]
fn mul_vec_bits_vs_k() {
    let m = SparseMatrix::new(
        2,
        3,
        [
            ((0, 1), K::from_u128(5)),
            ((0, 2), K::from_u128(7)),
            ((3, 7), K::from_u128(9)),
        ],
    );
    let z = [false, true, true, false, false, false, false, true];
    let zk: Vec<K> = z.iter().map(|&b| K::from_bit(b)).collect();
    assert_eq!(m.mul_vec_bits(&z), m.mul_vec(&zk));
    assert_eq!(m.mul_vec_bits(&z)[0], K::from_u128(5) + K::from_u128(7));
}

#[test]
fn toy_satisfied_and_not() {
    let mut r = rng();
    let rels = common::structs();
    let (mut w, x, _) = common::witness(&mut r, 4, 0);
    assert!(simd_satisfied(&rels, &w, &x));
    w[2][common::OUT] ^= true;
    assert!(!simd_satisfied(&rels, &w, &x));
    let (mut w, x, _) = common::witness(&mut r, 4, 0);
    w[1][common::YC + 1] ^= true;
    assert!(!simd_satisfied(&rels, &w, &x));
}

#[test]
fn next_mle_matches_bruteforce() {
    let mut r = rng();
    for s in 0..4 {
        let a = r.ks(s);
        let b = r.ks(s);
        let n = 1usize << s;
        let mut tbl = vec![false; n * n];
        for i in 0..n.saturating_sub(1) {
            tbl[i + n * (i + 1)] = true;
        }
        let mut point = a.clone();
        point.extend_from_slice(&b);
        assert_eq!(next_mle(&a, &b), mle_eval_bits(&tbl, &point));
    }
}

// -------------------------------------------------------- TestSingleSpartan

fn public_input_rel() -> R1CS {
    // nu=3: z = (w0..w3, 1, x0, 0, 0). Row 0: w0 * w1 = x0; row 1: (w2 + w3) * 1 = w0.
    let one = K::ONE;
    R1CS::new(
        RelationField::B,
        1,
        3,
        SparseMatrix::new(1, 3, [((0, 0), one), ((1, 2), one), ((1, 3), one)]),
        SparseMatrix::new(1, 3, [((0, 1), one), ((1, 4), one)]),
        SparseMatrix::new(1, 3, [((0, 5), one), ((1, 0), one)]),
    )
}

fn run_single(rels: &[R1CS], w: &[Vec<bool>], x: &[Vec<K>], q: usize) -> SpartanProof {
    let s = q.trailing_zeros() as usize;
    let (proof, claims) = prove(rels, w, x, &mut fresh(), b"vsp", None, None, None, false);
    let out = verify(rels, s, x, &proof, &mut fresh(), b"vsp", None, None, None).unwrap();
    assert_eq!(out.len(), 1);
    assert_eq!(claims[0].value, out[0].value);
    assert_eq!(mle_eval_bits(&flatten_w(w), &out[0].point), out[0].value);
    proof
}

#[test]
fn bin_only_simd() {
    let mut r = rng();
    let (w, x, _) = common::witness(&mut r, 4, 0);
    let rels = common::structs();
    run_single(&rels[..1], &w, &x, 4);
}

#[test]
fn fld_only() {
    let mut r = rng();
    let (w, x, _) = common::witness(&mut r, 2, 0);
    let rels = common::structs();
    run_single(&rels[1..2], &w, &x, 2);
}

#[test]
fn single_instance() {
    let mut r = rng();
    let (w, x, _) = common::witness(&mut r, 1, 0);
    let rels = common::structs();
    run_single(&rels[..1], &w, &x, 1);
}

#[test]
fn public_inputs() {
    let mut r = rng();
    let rel = public_input_rel();
    let (mut w, mut x): (Vec<Vec<bool>>, Vec<Vec<K>>) = (Vec::new(), Vec::new());
    for _ in 0..4 {
        let (w0, w1, w3) = (r.bit(), r.bit(), r.bit());
        let w2 = w0 ^ w3;
        w.push(vec![w0, w1, w2, w3]);
        x.push(vec![K::from_bit(w0 && w1)]);
    }
    let rels = [rel];
    assert!(simd_satisfied(&rels, &w, &x));
    run_single(&rels, &w, &x, 4);
    // Wrong public input: the verifier rejects the honest proof.
    let (proof, _) = prove(&rels, &w, &x, &mut fresh(), b"vsp", None, None, None, false);
    x[1][0] += K::ONE;
    assert!(verify(&rels, 2, &x, &proof, &mut fresh(), b"vsp", None, None, None).is_err());
}

#[test]
fn unsatisfied_single() {
    let mut r = rng();
    let rels = common::structs();
    let rels = &rels[..1];
    let (mut w, x, _) = common::witness(&mut r, 4, 0);
    w[3][common::OUT + 2] ^= true;
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove(rels, &w, &x, &mut fresh(), b"vsp", None, None, None, false)
    }));
    assert!(
        res.is_err(),
        "honest prover must refuse an unsatisfied witness"
    );
    let (proof, _) = prove(rels, &w, &x, &mut fresh(), b"vsp", None, None, None, true);
    assert!(verify(rels, 2, &x, &proof, &mut fresh(), b"vsp", None, None, None).is_err());
}

#[test]
fn tamper_single() {
    let mut r = rng();
    let rels = common::structs();
    let rels = &rels[..1];
    let (w, x, _) = common::witness(&mut r, 4, 0);
    let (proof, _) = prove(rels, &w, &x, &mut fresh(), b"vsp", None, None, None, false);
    let mut tampered: Vec<SpartanProof> = Vec::new();
    let mut p2 = proof.clone();
    p2.outer_msgs[0][1][0] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.outer_finals[0][2] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.inner.round_msgs[2][1] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.v_w += K::ONE;
    tampered.push(p2);
    for p2 in &tampered {
        assert!(verify(rels, 2, &x, p2, &mut fresh(), b"vsp", None, None, None).is_err());
    }
}

// ------------------------------------------------------- TestVirtualSpartan

struct Vsp {
    rels: Vec<R1CS>,
    segs: Vec<Segment>,
    w: Vec<Vec<bool>>,
    x: Vec<Vec<K>>,
    cross: CrossStep,
}

fn vsp_setup() -> Vsp {
    let mut r = rng();
    let (w, x, cross) = common::witness(&mut r, 4, 0);
    Vsp {
        rels: common::structs(),
        segs: common::segments(),
        w,
        x,
        cross,
    }
}

impl Vsp {
    fn prove(&self, unchecked: bool) -> (SpartanProof, Vec<om_spartan::spartan::Claim>) {
        prove(
            &self.rels,
            &self.w,
            &self.x,
            &mut fresh(),
            b"vsp",
            None,
            Some(&self.segs),
            Some(&self.cross),
            unchecked,
        )
    }

    fn verify(
        &self,
        proof: &SpartanProof,
    ) -> Result<Vec<om_spartan::spartan::Claim>, om_sumcheck::VerificationError> {
        verify(
            &self.rels,
            2,
            &self.x,
            proof,
            &mut fresh(),
            b"vsp",
            None,
            Some(&self.segs),
            Some(&self.cross),
        )
    }
}

#[test]
fn vsp_completeness_and_claims() {
    let v = vsp_setup();
    let (proof, claims) = v.prove(false);
    let out = v.verify(&proof).unwrap();
    let triples = |cs: &[om_spartan::spartan::Claim]| {
        cs.iter()
            .map(|c| (c.comp_id, c.point.clone(), c.value))
            .collect::<Vec<_>>()
    };
    assert_eq!(triples(&claims), triples(&out));
    // 7 non-pad segments + 2 cross-step claims.
    assert_eq!(out.len(), 9);
    for c in &out {
        let sg = v.segs.iter().find(|s| s.seg_id == c.comp_id).unwrap();
        let tbl = segment_table(&v.w, sg);
        assert_eq!(mle_eval_bits(&tbl, &c.point), c.value);
    }
    let pts: Vec<&Vec<K>> = out
        .iter()
        .filter(|c| c.comp_id == common::SEG_IN)
        .map(|c| &c.point)
        .collect();
    assert_eq!(pts.len(), 2);
    assert_ne!(pts[0], pts[1]);
}

#[test]
fn vsp_shared_instance_challenges() {
    let v = vsp_setup();
    let (_, claims) = v.prove(false);
    // All non-cross claims share the instance suffix (the last s=2 vars).
    let suffix = |c: &om_spartan::spartan::Claim| c.point[c.point.len() - 2..].to_vec();
    let first = suffix(&claims[0]);
    assert!(claims[..7].iter().all(|c| suffix(c) == first));
}

#[test]
fn vsp_other_sizes() {
    let mut r = rng();
    let rels = common::structs();
    let segs = common::segments();
    for q in [1usize, 2, 8] {
        let (w, x, cross) = common::witness(&mut r, q, 0);
        let (proof, _) = prove(
            &rels,
            &w,
            &x,
            &mut fresh(),
            b"vsp",
            None,
            Some(&segs),
            Some(&cross),
            false,
        );
        verify(
            &rels,
            q.trailing_zeros() as usize,
            &x,
            &proof,
            &mut fresh(),
            b"vsp",
            None,
            Some(&segs),
            Some(&cross),
        )
        .unwrap();
    }
}

#[test]
fn vsp_nonzero_init() {
    let mut r = rng();
    let rels = common::structs();
    let segs = common::segments();
    let (w, x, cross) = common::witness(&mut r, 4, 9);
    let (proof, _) = prove(
        &rels,
        &w,
        &x,
        &mut fresh(),
        b"vsp",
        None,
        Some(&segs),
        Some(&cross),
        false,
    );
    verify(
        &rels,
        2,
        &x,
        &proof,
        &mut fresh(),
        b"vsp",
        None,
        Some(&segs),
        Some(&cross),
    )
    .unwrap();
}

#[test]
fn vsp_unsatisfied_bin_constraint() {
    let mut v = vsp_setup();
    v.w[1][common::CARRY + 1] ^= true;
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| v.prove(false)));
    assert!(res.is_err());
    let (proof, _) = v.prove(true);
    assert!(v.verify(&proof).is_err());
}

#[test]
fn vsp_unsatisfied_fld_constraint() {
    let mut v = vsp_setup();
    v.w[2][common::YC] ^= true;
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| v.prove(false)));
    assert!(res.is_err());
    let (proof, _) = v.prove(true);
    assert!(v.verify(&proof).is_err());
}

#[test]
fn vsp_inconsistent_cross_step() {
    let mut r = rng();
    let v = vsp_setup();
    // Every row satisfies both relations, but IN[j] != OUT[j-1] at j = 2.
    let mut w: Vec<Vec<bool>> = [0u32, 0, 7, 0]
        .iter()
        .map(|&init| {
            common::witness(&mut r, 1, init)
                .0
                .into_iter()
                .next()
                .unwrap()
        })
        .collect();
    let out_prev: u32 = (0..4).map(|i| u32::from(w[1][common::OUT + i]) << i).sum();
    if out_prev == 7 {
        w[2] = common::witness(&mut r, 1, 6).0.into_iter().next().unwrap();
    }
    assert!(simd_satisfied(&v.rels, &w, &v.x));
    let cross = CrossStep {
        in_id: common::SEG_IN,
        out_id: common::SEG_OUT,
        init: vec![false; 4],
        fin: (0..4).map(|i| w[3][common::OUT + i]).collect(),
    };
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove(
            &v.rels,
            &w,
            &v.x,
            &mut fresh(),
            b"vsp",
            None,
            Some(&v.segs),
            Some(&cross),
            false,
        )
    }));
    assert!(res.is_err(), "honest prover must refuse a broken chain");
    let (proof, _) = prove(
        &v.rels,
        &w,
        &v.x,
        &mut fresh(),
        b"vsp",
        None,
        Some(&v.segs),
        Some(&cross),
        true,
    );
    assert!(
        verify(
            &v.rels,
            2,
            &v.x,
            &proof,
            &mut fresh(),
            b"vsp",
            None,
            Some(&v.segs),
            Some(&cross)
        )
        .is_err()
    );
}

#[test]
fn vsp_wrong_public_boundary() {
    let v = vsp_setup();
    let (proof, _) = v.prove(false);
    let bad_init = CrossStep {
        in_id: common::SEG_IN,
        out_id: common::SEG_OUT,
        init: vec![true, false, false, false],
        fin: v.cross.fin.clone(),
    };
    assert!(
        verify(
            &v.rels,
            2,
            &v.x,
            &proof,
            &mut fresh(),
            b"vsp",
            None,
            Some(&v.segs),
            Some(&bad_init)
        )
        .is_err()
    );
    let mut fin = v.cross.fin.clone();
    fin[2] ^= true;
    let bad_fin = CrossStep {
        in_id: common::SEG_IN,
        out_id: common::SEG_OUT,
        init: v.cross.init.clone(),
        fin,
    };
    assert!(
        verify(
            &v.rels,
            2,
            &v.x,
            &proof,
            &mut fresh(),
            b"vsp",
            None,
            Some(&v.segs),
            Some(&bad_fin)
        )
        .is_err()
    );
}

#[test]
fn vsp_tampered_segment_claim() {
    let v = vsp_setup();
    let (proof, _) = v.prove(false);
    for i in 0..proof.seg_vals.len() {
        let mut p2 = proof.clone();
        p2.seg_vals[i] += K::ONE;
        assert!(v.verify(&p2).is_err());
    }
}

#[test]
fn vsp_tampered_other_fields() {
    let v = vsp_setup();
    let (proof, _) = v.prove(false);
    let mut tampered: Vec<SpartanProof> = Vec::new();
    let mut p2 = proof.clone(); // fld instance round
    p2.outer_msgs[1][4][1] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone(); // bin row round
    p2.outer_msgs[0][0][2] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.outer_finals[1][0] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.inner.round_msgs[0][0] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.v_w += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.xs_vals.as_mut().unwrap()[0] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.xs_vals.as_mut().unwrap()[1] += K::ONE;
    tampered.push(p2);
    let mut p2 = proof.clone();
    p2.xs_proof.as_mut().unwrap().round_msgs[1][0] += K::ONE;
    tampered.push(p2);
    for p2 in &tampered {
        assert!(v.verify(p2).is_err());
    }
}

#[test]
fn vsp_nonzero_padding_rejected() {
    let mut v = vsp_setup();
    v.w[1][28] = true; // a padding column (segment SEG_PAD); no constraint touches it
    let (proof, _) = v.prove(false);
    assert!(v.verify(&proof).is_err());
    v.w[1][28] = false;
    v.w[1][26] = true; // an implicitly uncovered column
    let (proof, _) = v.prove(false);
    assert!(v.verify(&proof).is_err());
}

#[test]
#[should_panic]
fn vsp_bad_layout_rejected() {
    let v = vsp_setup();
    let mut bad = v.segs.clone();
    bad.push(Segment {
        seg_id: 99,
        kind: SegmentKind::Direct,
        log_cols: 2,
        block: 0,
    });
    check_layout(&bad, common::NU);
}
