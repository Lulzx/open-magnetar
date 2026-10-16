//! Port of `reference/tests/test_mosaic.py`, plus the 256-claim cap
//! (spec 05 §5.4) which the Python suite enforces in code but does
//! not test.

use std::collections::BTreeMap;

use om_field::K;
use om_mosaic::{
    BatchProof, Claim, MAX_CLAIMS, batch_prove, batch_prove_packed, batch_verify, build_g,
    build_g_packed, compute_layout, lift_point,
};
use om_sumcheck::mle_eval_bits;
use om_transcript::Transcript;

/// Deterministic splitmix64 stream (no `rand` crate), as in the other
/// crates' tests; stands in for Python's `random.Random(77)`.
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
        K::from_u128(u128::from(self.next_u64()) | (u128::from(self.next_u64()) << 64))
    }
    fn ks(&mut self, n: usize) -> Vec<K> {
        (0..n).map(|_| self.k()).collect()
    }
    fn bit(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

const COMPS: [(i64, usize); 7] = [(5, 3), (2, 4), (9, 3), (1, 0), (7, 1), (3, 4), (4, 2)];

fn setup(
    rng: &mut Rng,
    ell_min: usize,
) -> (om_mosaic::Layout, BTreeMap<i64, Vec<bool>>, Vec<bool>) {
    let lay = compute_layout(&COMPS, ell_min);
    let tables: BTreeMap<i64, Vec<bool>> = COMPS
        .iter()
        .map(|&(cid, ls)| (cid, (0..1usize << ls).map(|_| rng.bit()).collect()))
        .collect();
    let g = build_g(&lay, &tables);
    (lay, tables, g)
}

fn claims(rng: &mut Rng, tables: &BTreeMap<i64, Vec<bool>>) -> Vec<Claim> {
    // Component 2 gets three claims (COMPS + [(2, 4), (2, 4)]).
    let mut cs = COMPS.to_vec();
    cs.extend_from_slice(&[(2, 4), (2, 4)]);
    cs.iter()
        .map(|&(cid, ls)| {
            let r = rng.ks(ls);
            Claim {
                comp_id: cid,
                value: mle_eval_bits(&tables[&cid], &r),
                point: r,
            }
        })
        .collect()
}

#[test]
fn layout_order_alignment_disjoint() {
    let mut rng = Rng(77);
    let (lay, _, _) = setup(&mut rng, 0);
    let order: Vec<i64> = lay.placements.iter().map(|p| p.comp_id).collect();
    assert_eq!(order, vec![2, 3, 5, 9, 4, 7, 1]);
    let total: usize = COMPS.iter().map(|&(_, ls)| 1usize << ls).sum(); // 55
    assert_eq!(lay.ell, 6);
    assert!((1usize << lay.ell) >= total);
    let mut end = 0;
    for p in &lay.placements {
        assert_eq!(p.offset % (1usize << p.log_size), 0);
        assert_eq!(p.offset, end);
        assert_eq!(p.suffix, p.offset >> p.log_size);
        end += 1usize << p.log_size;
    }
}

#[test]
fn layout_ell_min_and_order_independence() {
    let a = compute_layout(&COMPS, 9);
    let mut rev = COMPS;
    rev.reverse();
    let b = compute_layout(&rev, 9);
    assert_eq!(a, b);
    assert_eq!(a.ell, 9);
}

#[test]
fn layout_single() {
    assert_eq!(compute_layout(&[(1, 0)], 0).ell, 0);
}

#[test]
#[should_panic(expected = "duplicate component id")]
fn layout_duplicates_rejected() {
    compute_layout(&[(1, 2), (1, 3)], 0);
}

#[test]
#[should_panic(expected = "empty component list")]
fn layout_empty_rejected() {
    compute_layout(&[], 0);
}

#[test]
#[should_panic(expected = "bad component")]
fn layout_negative_id_rejected() {
    // In particular the Spartan whole-W sentinel -1 is no component.
    compute_layout(&[(-1, 2)], 0);
}

#[test]
#[should_panic(expected = "bad component")]
fn layout_id_at_2_pow_32_rejected() {
    compute_layout(&[(1i64 << 32, 2)], 0);
}

#[test]
fn lifting_eq4() {
    let mut rng = Rng(77);
    let (lay, tables, g) = setup(&mut rng, 0);
    for &(cid, ls) in &COMPS {
        let r = rng.ks(ls);
        let c = Claim {
            comp_id: cid,
            value: mle_eval_bits(&tables[&cid], &r),
            point: r,
        };
        assert_eq!(mle_eval_bits(&g, &lift_point(&lay, &c).unwrap()), c.value);
    }
}

#[test]
fn batching_completeness() {
    let mut rng = Rng(77);
    let (lay, tables, g) = setup(&mut rng, 0);
    let cl = claims(&mut rng, &tables);
    let (proof, r_g, v_g) = batch_prove(&lay, &cl, &g, &mut Transcript::new_default(b"m"));
    let (r_g2, v_g2) = batch_verify(&lay, &cl, &proof, &mut Transcript::new_default(b"m")).unwrap();
    assert_eq!((&r_g, v_g), (&r_g2, v_g2));
    assert_eq!(mle_eval_bits(&g, &r_g), v_g);
}

#[test]
fn batching_negative() {
    let mut rng = Rng(77);
    let (lay, tables, g) = setup(&mut rng, 0);
    let cl = claims(&mut rng, &tables);
    let (proof, _, _) = batch_prove(&lay, &cl, &g, &mut Transcript::new_default(b"m"));

    let mut p2 = proof.clone();
    p2.sumcheck.round_msgs[2][0] += K::ONE;
    assert!(batch_verify(&lay, &cl, &p2, &mut Transcript::new_default(b"m")).is_err());

    let p2 = BatchProof {
        v_g: proof.v_g + K::ONE,
        ..proof.clone()
    };
    assert!(batch_verify(&lay, &cl, &p2, &mut Transcript::new_default(b"m")).is_err());

    let mut cl2 = cl.clone();
    cl2[3] = Claim {
        value: cl[3].value + K::ONE,
        ..cl[3].clone()
    };
    assert!(batch_verify(&lay, &cl2, &proof, &mut Transcript::new_default(b"m")).is_err());

    let unknown = vec![Claim {
        comp_id: 1234,
        point: vec![],
        value: K::ZERO,
    }];
    assert!(batch_verify(&lay, &unknown, &proof, &mut Transcript::new_default(b"m")).is_err());

    let wrong_len = vec![Claim {
        comp_id: 2,
        point: vec![K::ONE],
        value: K::ZERO,
    }];
    assert!(batch_verify(&lay, &wrong_len, &proof, &mut Transcript::new_default(b"m")).is_err());
}

#[test]
#[should_panic]
fn false_claim_not_provable() {
    let mut rng = Rng(77);
    let (lay, tables, g) = setup(&mut rng, 0);
    let mut cl = claims(&mut rng, &tables);
    cl[0] = Claim {
        value: cl[0].value + K::ONE,
        ..cl[0].clone()
    };
    batch_prove(&lay, &cl, &g, &mut Transcript::new_default(b"m"));
}

#[test]
fn claim_cap_at_256_accepted() {
    let mut rng = Rng(77);
    let (lay, tables, g) = setup(&mut rng, 0);
    let cl: Vec<Claim> = (0..MAX_CLAIMS)
        .map(|i| {
            let (cid, ls) = COMPS[i % COMPS.len()];
            let r = rng.ks(ls);
            Claim {
                comp_id: cid,
                value: mle_eval_bits(&tables[&cid], &r),
                point: r,
            }
        })
        .collect();
    let (proof, r_g, v_g) = batch_prove(&lay, &cl, &g, &mut Transcript::new_default(b"m"));
    let out = batch_verify(&lay, &cl, &proof, &mut Transcript::new_default(b"m")).unwrap();
    assert_eq!(out, (r_g, v_g));
}

#[test]
#[should_panic(expected = "too many Mosaic claims")]
fn claim_cap_300_prove_rejected() {
    let mut rng = Rng(77);
    let (lay, _, g) = setup(&mut rng, 0);
    let cl = vec![
        Claim {
            comp_id: 1,
            point: vec![],
            value: K::ZERO,
        };
        300
    ];
    batch_prove(&lay, &cl, &g, &mut Transcript::new_default(b"m"));
}

#[test]
fn claim_cap_300_verify_rejected() {
    let mut rng = Rng(77);
    let (lay, tables, g) = setup(&mut rng, 0);
    let cl = claims(&mut rng, &tables);
    let (proof, _, _) = batch_prove(&lay, &cl, &g, &mut Transcript::new_default(b"m"));
    let many = vec![
        Claim {
            comp_id: 1,
            point: vec![],
            value: K::ZERO,
        };
        300
    ];
    let err = batch_verify(&lay, &many, &proof, &mut Transcript::new_default(b"m")).unwrap_err();
    assert!(err.message().contains("too many Mosaic claims"), "{err}");
}

#[test]
fn batching_packed_matches_bool() {
    let mut rng = Rng(77);
    let (lay, tables, g) = setup(&mut rng, 0);
    let cl = claims(&mut rng, &tables);
    // The packed assembly is the same bits.
    let packed_tables: BTreeMap<i64, om_sumcheck::PackedBits> = tables
        .iter()
        .map(|(&cid, tb)| (cid, om_sumcheck::PackedBits::from_bools(tb)))
        .collect();
    let g_packed = build_g_packed(&lay, &packed_tables);
    assert_eq!(g_packed.to_bools(), g);
    // And the packed batch proof is byte-identical to the bool one.
    let (p1, r1, v1) = batch_prove(&lay, &cl, &g, &mut Transcript::new_default(b"m"));
    let (p2, r2, v2) = batch_prove_packed(&lay, &cl, &g_packed, &mut Transcript::new_default(b"m"));
    assert_eq!((p1, r1, v1), (p2, r2, v2));
}
