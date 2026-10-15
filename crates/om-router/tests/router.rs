//! Port of `reference/tests/test_router.py` in full, plus the
//! fast-vs-dense prover equality of `test_protocol.py::TestFastRouters`.
//! Shapes and assertions match the Python tests; randomness comes from
//! the deterministic `common::Rng` (byte-exact behavior is pinned by
//! `tests/vectors.rs`).

mod common;

use std::collections::{HashMap, HashSet};

use common::Rng;
use om_field::K;
use om_router::router::{
    RouterProof, ShiftCycle, ShiftWitness, StoreCycle, StoreWitness, apply_shift, apply_store,
    shift_entries, shift_prove, shift_prove_fast, shift_r_eval, shift_valid, shift_verify,
    shift_witness, store_entries, store_prove, store_prove_fast, store_r_eval, store_valid,
    store_verify, store_witness,
};
use om_sumcheck::{VerificationError, mle_eval_bits};
use om_transcript::Transcript;

fn tr() -> Transcript {
    Transcript::new_default(b"test/router")
}

fn concat(a: &[K], b: &[K]) -> Vec<K> {
    [a, b].concat()
}

// ------------------------------------------------------------- ShiftSpecTest

#[test]
fn shift_entries_match_semantics_64() {
    let mut rng = Rng(1);
    let ent = shift_entries(6);
    let mut by_h: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    for (o, u, h) in &ent {
        by_h.entry(*h).or_default().push((*o, *u));
    }
    // each output has at most one source
    for lst in by_h.values() {
        let os: Vec<usize> = lst.iter().map(|&(o, _)| o).collect();
        let unique: HashSet<usize> = os.iter().copied().collect();
        assert_eq!(os.len(), unique.len());
    }
    assert_eq!(ent.len(), 12512);
    for kind in 0..8 {
        for amt in 0..64 {
            let h = amt + 64 * kind;
            if !shift_valid(kind, amt, 6) {
                assert!(!by_h.contains_key(&h));
                continue;
            }
            for _ in 0..3 {
                let src = rng.word(64);
                let mut y = 0u64;
                for &(o, u) in by_h.get(&h).map_or(&[][..], Vec::as_slice) {
                    y |= ((src >> u) & 1) << o;
                }
                assert_eq!(
                    y,
                    apply_shift(kind, amt, src, 6),
                    "({}, {amt})",
                    om_router::KIND_NAMES[kind]
                );
            }
        }
    }
}

#[test]
fn shift_known_values() {
    assert_eq!(
        apply_shift(2, 4, 0x8000_0000_0000_0000, 6),
        0xF800_0000_0000_0000
    );
    assert_eq!(apply_shift(3, 1, 0x4000_0000, 6), 0xFFFF_FFFF_8000_0000);
    assert_eq!(apply_shift(4, 0, 0x8000_0000, 6), 0xFFFF_FFFF_8000_0000);
    assert_eq!(apply_shift(4, 1, 0x8000_0000, 6), 0x4000_0000);
    assert_eq!(apply_shift(5, 4, 0x8000_0000, 6), 0xFFFF_FFFF_F800_0000);
    assert_eq!(apply_shift(6, 0, 0x1_8000_0000, 6), 0xFFFF_FFFF_8000_0000);
    assert_eq!(apply_shift(7, 0, 0x1_8000_0000, 6), 0x8000_0000);
    assert_eq!(apply_shift(3, 32, 5, 6), 0);
    assert_eq!(apply_shift(6, 3, 5, 6), 0);
}

#[test]
fn shift_r_eval_matches_mle() {
    let mut rng = Rng(2);
    let wb = 3;
    let w = 1usize << wb;
    let mut table = vec![false; w * w * 8 * w]; // o + W*(u + W*h)
    for (o, u, h) in shift_entries(wb) {
        table[o + w * (u + w * h)] = true;
    }
    let pt = rng.ks(wb + wb + wb + 3);
    assert_eq!(
        shift_r_eval(&pt[..wb], &pt[wb..2 * wb], &pt[2 * wb..], wb),
        mle_eval_bits(&table, &pt)
    );
}

// ------------------------------------------------------------- StoreSpecTest

#[test]
fn store_entries_match_semantics_64() {
    let mut rng = Rng(3);
    let ent = store_entries(6);
    assert_eq!(ent.len(), 512);
    for h in 0..4 {
        for a in 0..8 {
            for _ in 0..3 {
                let (old, src) = (rng.word(64), rng.word(64));
                let mut y = 0u64;
                for &(o, u, hh, aa) in &ent {
                    if hh == h && aa == a {
                        let bit = if u < 64 {
                            (old >> u) & 1
                        } else {
                            (src >> (u - 64)) & 1
                        };
                        y ^= bit << o;
                    }
                }
                assert_eq!(y, apply_store(old, src, h, a, 6));
                if !store_valid(h, a, 6) {
                    assert_eq!(y, 0);
                }
            }
        }
    }
    // concrete cases
    assert_eq!(apply_store(0, 0xAABB_CCDD, 0, 3, 6), 0xDD << 24);
    assert_eq!(apply_store(0xFF << 24, 0xDD, 0, 3, 6), (0xFF ^ 0xDD) << 24);
    assert_eq!(
        apply_store(0, 0x1122_3344_5566_7788, 2, 4, 6),
        0x5566_7788 << 32
    );
}

#[test]
fn store_r_eval_matches_mle() {
    let mut rng = Rng(4);
    let wb = 4;
    let w = 1usize << wb;
    // index o + W*(u + 2W*(h + 4*a))
    let mut table = vec![false; w * 2 * w * 4 * 2];
    for (o, u, h, a) in store_entries(wb) {
        table[o + w * (u + 2 * w * (h + 4 * a))] = true;
    }
    let pt = rng.ks(wb + wb + 1 + 2 + 1);
    assert_eq!(
        store_r_eval(
            &pt[..wb],
            &pt[wb..2 * wb + 1],
            &pt[2 * wb + 1..2 * wb + 3],
            &pt[2 * wb + 3..],
            wb
        ),
        mle_eval_bits(&table, &pt)
    );
}

// ---------------------------------------------------------- ShiftProtocolTest

fn shift_case(n: usize, wb: usize, seed: u64) -> (ShiftWitness, Vec<K>, Vec<K>, K) {
    let mut rng = Rng(seed);
    let (w, t) = (1usize << wb, 1usize << n);
    let mut cycles = Vec::new();
    for _ in 0..t {
        let src = rng.word(w as u32);
        if rng.chance(1, 4) {
            cycles.push((src, None));
        } else {
            loop {
                let (kind, amt) = (rng.below(8), rng.below(w));
                if shift_valid(kind, amt, wb) {
                    cycles.push((src, Some((amt, kind))));
                    break;
                }
            }
        }
    }
    let wit = shift_witness(&cycles, wb);
    let r_o = rng.ks(wb);
    let r_j = rng.ks(n);
    let y = mle_eval_bits(&wit.y, &concat(&r_o, &r_j));
    (wit, r_o, r_j, y)
}

fn shift_check(n: usize, wb: usize, seed: u64) -> (ShiftWitness, Vec<K>, Vec<K>, K, RouterProof) {
    let (wit, r_o, r_j, y) = shift_case(n, wb, seed);
    let (proof, claims) = shift_prove(n, &wit, &r_o, &r_j, y, &mut tr(), b"sh", wb);
    let vc = shift_verify(n, &r_o, &r_j, y, &proof, &mut tr(), b"sh", wb).unwrap();
    assert_eq!(claims, vc);
    for c in &vc {
        let tab = match c.poly.as_str() {
            "shift/src" => &wit.x,
            "shift/qlo" => &wit.qlo,
            "shift/qhi" => &wit.qhi,
            other => panic!("bad poly {other}"),
        };
        assert_eq!(mle_eval_bits(tab, &c.point), c.value);
    }
    (wit, r_o, r_j, y, proof)
}

#[test]
fn shift_wb3() {
    shift_check(2, 3, 1);
}

#[test]
fn shift_wb3_n3() {
    shift_check(3, 3, 2);
}

#[test]
fn shift_wrong_output_claim() {
    let (_wit, r_o, r_j, y, proof) = shift_check(2, 3, 3);
    let err = shift_verify(2, &r_o, &r_j, y + K::ONE, &proof, &mut tr(), b"sh", 3).unwrap_err();
    let _: VerificationError = err;
}

#[test]
fn shift_wrong_shift_output() {
    // prover's Y has a flipped bit; claim built from that Y
    let (wit, r_o, r_j, _y) = shift_case(2, 3, 4);
    let mut bad_y = wit.y.clone();
    bad_y[5] = !bad_y[5];
    let y2 = mle_eval_bits(&bad_y, &concat(&r_o, &r_j));
    let (proof, _) = shift_prove(2, &wit, &r_o, &r_j, y2, &mut tr(), b"sh", 3);
    assert!(shift_verify(2, &r_o, &r_j, y2, &proof, &mut tr(), b"sh", 3).is_err());
}

#[test]
fn shift_nonshift_cycle_output_must_be_zero() {
    let wit = shift_witness(
        &[(0x5A, None), (0x5A, None), (0x33, Some((1, 0))), (1, None)],
        3,
    );
    let mut rng = Rng(9);
    let r_o = rng.ks(3);
    let r_j = rng.ks(2);
    let mut bad_y = wit.y.clone();
    bad_y[8] = true; // nonzero output on a cycle with zero selector (0 + 8*1)
    let y2 = mle_eval_bits(&bad_y, &concat(&r_o, &r_j));
    let (proof, _) = shift_prove(2, &wit, &r_o, &r_j, y2, &mut tr(), b"sh", 3);
    assert!(shift_verify(2, &r_o, &r_j, y2, &proof, &mut tr(), b"sh", 3).is_err());
}

#[test]
fn shift_wb6() {
    shift_check(1, 6, 5);
}

/// Extra negative: tampering with a claimed eval breaks the final check.
#[test]
fn shift_tampered_eval_rejected() {
    let (_wit, r_o, r_j, y, mut proof) = shift_check(2, 3, 11);
    proof.evals[0] += K::ONE;
    assert!(shift_verify(2, &r_o, &r_j, y, &proof, &mut tr(), b"sh", 3).is_err());
}

/// Extra negative: a truncated evals list is malformed before the
/// transcript is touched.
#[test]
fn shift_malformed_evals_rejected() {
    let (_wit, r_o, r_j, y, mut proof) = shift_check(2, 3, 12);
    proof.evals.pop();
    let err = shift_verify(2, &r_o, &r_j, y, &proof, &mut tr(), b"sh", 3).unwrap_err();
    assert_eq!(err.message(), "shift: malformed evals");
}

// ---------------------------------------------------------- StoreProtocolTest

fn store_case(
    n: usize,
    wb: usize,
    seed: u64,
    nonstore: (u64, u64),
) -> (StoreWitness, Vec<K>, Vec<K>, K) {
    let mut rng = Rng(seed);
    let (w, t) = (1usize << wb, 1usize << n);
    let nbytes = w / 8;
    let mut cycles = Vec::new();
    for _ in 0..t {
        let (old, src) = (rng.word(w as u32), rng.word(w as u32));
        if rng.chance(nonstore.0, nonstore.1) {
            cycles.push((old, src, None));
        } else {
            loop {
                let (h, a) = (rng.below(4), rng.below(nbytes));
                if store_valid(h, a, wb) {
                    cycles.push((old, src, Some((h, a))));
                    break;
                }
            }
        }
    }
    let wit = store_witness(&cycles, wb);
    let r_o = rng.ks(wb);
    let r_j = rng.ks(n);
    let y = mle_eval_bits(&wit.inc, &concat(&r_o, &r_j));
    (wit, r_o, r_j, y)
}

fn store_check(n: usize, wb: usize, seed: u64) -> (StoreWitness, Vec<K>, Vec<K>, K, RouterProof) {
    let (wit, r_o, r_j, y) = store_case(n, wb, seed, (1, 4));
    let (proof, claims) = store_prove(n, &wit, &r_o, &r_j, y, &mut tr(), b"st", wb);
    let vc = store_verify(n, &r_o, &r_j, y, &proof, &mut tr(), b"st", wb).unwrap();
    assert_eq!(claims, vc);
    for c in &vc {
        let tab = if c.poly == "store/src" {
            &wit.x
        } else if c.poly == "store/q" {
            &wit.q
        } else {
            let b: usize = c.poly["store/a".len()..].parse().unwrap();
            &wit.abits[b]
        };
        assert_eq!(mle_eval_bits(tab, &c.point), c.value);
    }
    (wit, r_o, r_j, y, proof)
}

#[test]
fn store_wb4() {
    store_check(2, 4, 1);
}

#[test]
fn store_wb5() {
    store_check(2, 5, 2);
}

#[test]
fn store_wb6() {
    store_check(1, 6, 3);
}

#[test]
fn store_wb6_n2() {
    store_check(2, 6, 4);
}

#[test]
fn store_wrong_increment_claim() {
    let (_wit, r_o, r_j, y, proof) = store_check(2, 4, 5);
    let err = store_verify(2, &r_o, &r_j, y + K::ONE, &proof, &mut tr(), b"st", 4).unwrap_err();
    let _: VerificationError = err;
}

#[test]
fn store_wrong_store_increment() {
    let (wit, r_o, r_j, _y) = store_case(2, 4, 6, (1, 4));
    let mut bad_inc = wit.inc.clone();
    bad_inc[3] = !bad_inc[3];
    let y2 = mle_eval_bits(&bad_inc, &concat(&r_o, &r_j));
    let (proof, _) = store_prove(2, &wit, &r_o, &r_j, y2, &mut tr(), b"st", 4);
    assert!(store_verify(2, &r_o, &r_j, y2, &proof, &mut tr(), b"st", 4).is_err());
}

#[test]
fn store_nonstore_cycle_inc_must_be_zero() {
    let wit = store_witness(
        &[
            (0xABCD, 0x1234, None),
            (0xABCD, 0x1234, Some((0, 1))),
            (7, 9, None),
            (0, 0, None),
        ],
        4,
    );
    let mut rng = Rng(10);
    let r_o = rng.ks(4);
    let r_j = rng.ks(2);
    let mut bad_inc = wit.inc.clone();
    bad_inc[2] = true; // increment on a cycle with an all-zero selector (2 + 16*0)
    let y2 = mle_eval_bits(&bad_inc, &concat(&r_o, &r_j));
    let (proof, _) = store_prove(2, &wit, &r_o, &r_j, y2, &mut tr(), b"st", 4);
    assert!(store_verify(2, &r_o, &r_j, y2, &proof, &mut tr(), b"st", 4).is_err());
}

#[test]
fn store_wrong_offset_witness() {
    // offset bits committed differently from the ones the increment used
    let (mut wit, r_o, r_j, y) = store_case(2, 4, 7, (0, 1));
    wit.abits[0] = wit.abits[0].iter().map(|&b| !b).collect();
    let (proof, _) = store_prove(2, &wit, &r_o, &r_j, y, &mut tr(), b"st", 4);
    assert!(store_verify(2, &r_o, &r_j, y, &proof, &mut tr(), b"st", 4).is_err());
}

/// Extra negative: tampering with a claimed offset eval breaks the
/// final check.
#[test]
fn store_tampered_eval_rejected() {
    let (_wit, r_o, r_j, y, mut proof) = store_check(2, 4, 13);
    let last = proof.evals.len() - 1;
    proof.evals[last] += K::ONE;
    assert!(store_verify(2, &r_o, &r_j, y, &proof, &mut tr(), b"st", 4).is_err());
}

// ------------------------------------------------- fast provers (TestFastRouters)

#[test]
fn fast_provers_equal_dense() {
    let mut rng = Rng(3);
    let (wb, n) = (4usize, 3usize);
    let t = 1usize << n;
    let cyc: Vec<ShiftCycle> = (0..t)
        .map(|_| {
            let src = rng.word(16);
            if rng.chance(2, 5) {
                (src, None)
            } else {
                (src, Some((rng.below(16), rng.below(3))))
            }
        })
        .collect();
    let w = shift_witness(&cyc, wb);
    let r_o = rng.ks(wb);
    let r_j = rng.ks(n);
    let y = mle_eval_bits(&w.y, &concat(&r_o, &r_j));
    let (a, a_claims) = shift_prove(
        n,
        &w,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(b"t"),
        b"s",
        wb,
    );
    let (b, b_claims) = shift_prove_fast(
        n,
        &w,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(b"t"),
        b"s",
        wb,
    );
    assert_eq!(a.sc.round_msgs, b.sc.round_msgs);
    assert_eq!(a.evals, b.evals);
    assert_eq!(a_claims, b_claims);
    // the fast proof also verifies under the (single) verifier
    shift_verify(
        n,
        &r_o,
        &r_j,
        y,
        &b,
        &mut Transcript::new_default(b"t"),
        b"s",
        wb,
    )
    .unwrap();

    let sc: Vec<StoreCycle> = (0..t)
        .map(|_| {
            let (old, src) = (rng.word(16), rng.word(16));
            if rng.chance(1, 2) {
                (old, src, None)
            } else {
                // Python's (h = randrange(3), randrange(2) << h), keeping
                // only offsets representable in the na = 1 offset bit (an
                // offset of 2 or 4 would be witnessed as 0 in `abits`,
                // which the Python seed's stream happens never to produce
                // for a width that has R entries).
                loop {
                    let h = rng.below(3);
                    let a = rng.below(2) << h;
                    if a < 2 {
                        break (old, src, Some((h, a)));
                    }
                }
            }
        })
        .collect();
    let ws = store_witness(&sc, wb);
    let y = mle_eval_bits(&ws.inc, &concat(&r_o, &r_j));
    let (a, a_claims) = store_prove(
        n,
        &ws,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(b"t"),
        b"s",
        wb,
    );
    let (b, b_claims) = store_prove_fast(
        n,
        &ws,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(b"t"),
        b"s",
        wb,
    );
    assert_eq!(a.sc.round_msgs, b.sc.round_msgs);
    assert_eq!(a.evals, b.evals);
    assert_eq!(a_claims, b_claims);
    store_verify(
        n,
        &r_o,
        &r_j,
        y,
        &b,
        &mut Transcript::new_default(b"t"),
        b"s",
        wb,
    )
    .unwrap();
}

/// Fast provers at the specification width (`wbits = 6`), where the
/// dense prover is the reference Python's ~10 s case.
#[test]
fn fast_provers_wb6_verify() {
    let (wit, r_o, r_j, y) = shift_case(2, 6, 21);
    let (proof, claims) = shift_prove_fast(2, &wit, &r_o, &r_j, y, &mut tr(), b"sh", 6);
    let vc = shift_verify(2, &r_o, &r_j, y, &proof, &mut tr(), b"sh", 6).unwrap();
    assert_eq!(claims, vc);

    let (wit, r_o, r_j, y) = store_case(2, 6, 22, (1, 4));
    let (proof, claims) = store_prove_fast(2, &wit, &r_o, &r_j, y, &mut tr(), b"st", 6);
    let vc = store_verify(2, &r_o, &r_j, y, &proof, &mut tr(), b"st", 6).unwrap();
    assert_eq!(claims, vc);
}
