//! The compact-witness router provers (`shift_prove_compact`,
//! `store_prove_compact`) against the dense definition (`shift_prove`,
//! `store_prove`): identical round messages, evals and claims for every
//! number of direct cycle rounds, including sparse selectors and
//! selectors with only one factor set.

mod common;

use common::Rng;
use om_router::router::{
    NO_ROUTE, ShiftCompact, ShiftCycle, StoreCompact, StoreCycle, shift_prove,
    shift_prove_compact_with, shift_valid, shift_verify, shift_witness, store_prove,
    store_prove_compact_with, store_valid, store_verify, store_witness,
};
use om_sumcheck::mle_eval_bits;
use om_transcript::Transcript;

fn tr() -> Transcript {
    Transcript::new_default(b"test/router/compact")
}

fn shift_cycles(rng: &mut Rng, n: usize, wb: usize, none: (u64, u64)) -> Vec<ShiftCycle> {
    let w = 1usize << wb;
    (0..1usize << n)
        .map(|_| {
            let src = rng.word(w as u32);
            if rng.chance(none.0, none.1) {
                return (src, None);
            }
            loop {
                let (kind, amt) = (rng.below(8), rng.below(w));
                if shift_valid(kind, amt, wb) {
                    break (src, Some((amt, kind)));
                }
            }
        })
        .collect()
}

fn shift_equal(n: usize, wb: usize, seed: u64, none: (u64, u64), half_selectors: bool) {
    let mut rng = Rng(seed);
    let cycles = shift_cycles(&mut rng, n, wb, none);
    let mut wit = shift_witness(&cycles, wb);
    let mut compact = ShiftCompact::from_cycles(&cycles);
    if half_selectors {
        // Cycle 1 keeps only its amount, cycle 2 only its kind: the
        // selector factors are separate multilinear tables.
        let w = 1usize << wb;
        wit.qhi[8..16].fill(false);
        compact.kind[1] = NO_ROUTE;
        wit.qlo[2 * w..3 * w].fill(false);
        compact.amt[2] = NO_ROUTE;
    }
    assert_eq!(ShiftCompact::from_witness(&wit, wb), compact);
    let r_o = rng.ks(wb);
    let r_j = rng.ks(n);
    let y = mle_eval_bits(&wit.y, &[&r_o[..], &r_j[..]].concat());
    let (a, ac) = shift_prove(n, &wit, &r_o, &r_j, y, &mut tr(), b"sh", wb);
    for direct in 0..=n + 1 {
        let (b, bc) =
            shift_prove_compact_with(n, &compact, &r_o, &r_j, y, &mut tr(), b"sh", wb, direct);
        assert_eq!(a, b, "shift n={n} wb={wb} direct={direct}");
        assert_eq!(ac, bc);
    }
    if !half_selectors {
        shift_verify(n, &r_o, &r_j, y, &a, &mut tr(), b"sh", wb).unwrap();
    }
}

fn store_cycles(rng: &mut Rng, n: usize, wb: usize, none: (u64, u64)) -> Vec<StoreCycle> {
    let w = 1usize << wb;
    (0..1usize << n)
        .map(|_| {
            let (old, src) = (rng.word(w as u32), rng.word(w as u32));
            if rng.chance(none.0, none.1) {
                return (old, src, None);
            }
            loop {
                let (h, a) = (rng.below(4), rng.below(w / 8));
                if store_valid(h, a, wb) {
                    break (old, src, Some((h, a)));
                }
            }
        })
        .collect()
}

fn store_equal(n: usize, wb: usize, seed: u64, none: (u64, u64), offsets_everywhere: bool) {
    let mut rng = Rng(seed);
    let cycles = store_cycles(&mut rng, n, wb, none);
    let mut wit = store_witness(&cycles, wb);
    let mut compact = StoreCompact::from_cycles(&cycles);
    if offsets_everywhere {
        // As in the prover: the offset bits are defined on every cycle.
        let na = wb - 3;
        for j in 0..cycles.len() {
            if cycles[j].2.is_none() {
                let off = rng.below(w_bytes(wb)) as u8;
                compact.off[j] = off;
                for (b, tab) in wit.abits.iter_mut().enumerate().take(na) {
                    tab[j] = (off >> b) & 1 == 1;
                }
            }
        }
    }
    assert_eq!(StoreCompact::from_witness(&wit, wb), compact);
    let r_o = rng.ks(wb);
    let r_j = rng.ks(n);
    let y = mle_eval_bits(&wit.inc, &[&r_o[..], &r_j[..]].concat());
    let (a, ac) = store_prove(n, &wit, &r_o, &r_j, y, &mut tr(), b"st", wb);
    for direct in 0..=n + 1 {
        let (b, bc) =
            store_prove_compact_with(n, &compact, &r_o, &r_j, y, &mut tr(), b"st", wb, direct);
        assert_eq!(a, b, "store n={n} wb={wb} direct={direct}");
        assert_eq!(ac, bc);
    }
    store_verify(n, &r_o, &r_j, y, &a, &mut tr(), b"st", wb).unwrap();
}

fn w_bytes(wb: usize) -> usize {
    (1usize << wb) / 8
}

#[test]
fn shift_compact_equals_dense_wb4() {
    shift_equal(6, 4, 1, (1, 4), false);
    shift_equal(5, 4, 2, (7, 8), false);
    shift_equal(5, 4, 3, (1, 1), false); // no shifts at all
    shift_equal(4, 4, 4, (1, 3), true);
}

#[test]
fn shift_compact_equals_dense_wb6() {
    shift_equal(3, 6, 5, (1, 2), false);
}

#[test]
fn store_compact_equals_dense() {
    store_equal(6, 4, 6, (1, 4), false);
    store_equal(6, 5, 7, (3, 4), true);
    store_equal(5, 6, 8, (1, 2), true);
    store_equal(4, 6, 9, (1, 1), true); // no stores at all
}
