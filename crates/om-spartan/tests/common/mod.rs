//! Shared helpers for the om-spartan integration tests: a deterministic
//! RNG and a port of `reference/openmagnetar/toy_cpu.py` (the toy
//! two-relation accumulator used by `test_spartan.py` and the 06
//! vectors).
#![allow(dead_code)]

use om_field::K;
use om_spartan::r1cs::{R1CS, RelationField, SparseMatrix};
use om_spartan::spartan::{CrossStep, Segment, SegmentKind};

/// Deterministic splitmix64 stream (no `rand` crate), as in om-pcs tests.
pub struct Rng(pub u64);

impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    pub fn k(&mut self) -> K {
        K::from_u128(u128::from(self.next_u64()) | (u128::from(self.next_u64()) << 64))
    }
    pub fn ks(&mut self, n: usize) -> Vec<K> {
        (0..n).map(|_| self.k()).collect()
    }
    pub fn bit(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
    /// `getrandbits(n)` for `n <= 32`, as used by the Python tests.
    pub fn bits_u32(&mut self, n: u32) -> u32 {
        (self.next_u64() & ((1u64 << n) - 1)) as u32
    }
}

// ---------------------------------------------------------------- toy CPU
// Port of reference/openmagnetar/toy_cpu.py: nu = 6 (64 z columns, 32
// witness columns), rho = 3 (8 rows).

pub const RHO: usize = 3;
pub const NU: usize = 6;
pub const ONE: usize = 1 << (NU - 1);
pub const IN: usize = 0;
pub const OUT: usize = 4;
pub const A: usize = 8;
pub const CARRY: usize = 12;
pub const XC: usize = 16;
pub const YC: usize = 20;
pub const SEL: usize = 24;

pub const SEG_IN: i64 = 1;
pub const SEG_OUT: i64 = 2;
pub const SEG_A: i64 = 3;
pub const SEG_CARRY: i64 = 4;
pub const SEG_X: i64 = 5;
pub const SEG_Y: i64 = 6;
pub const SEG_SEL: i64 = 7;
pub const SEG_PAD: i64 = 8;

pub fn structs() -> Vec<R1CS> {
    let mut a: Vec<((usize, usize), K)> = Vec::new();
    let mut b: Vec<((usize, usize), K)> = Vec::new();
    let mut c: Vec<((usize, usize), K)> = Vec::new();
    b.push(((0, ONE), K::ONE));
    a.push(((0, CARRY), K::ONE));
    for i in 0..4 {
        let r = 1 + i;
        for col in [IN + i, A + i, CARRY + i, OUT + i] {
            a.push(((r, col), K::ONE));
        }
        b.push(((r, ONE), K::ONE));
    }
    for i in 0..3 {
        let r = 5 + i;
        a.push(((r, IN + i), K::ONE));
        a.push(((r, CARRY + i), K::ONE));
        b.push(((r, A + i), K::ONE));
        b.push(((r, CARRY + i), K::ONE));
        c.push(((r, CARRY + i + 1), K::ONE));
        c.push(((r, CARRY + i), K::ONE));
    }
    let bin = R1CS::new(
        RelationField::B,
        RHO,
        NU,
        SparseMatrix::new(RHO, NU, a),
        SparseMatrix::new(RHO, NU, b),
        SparseMatrix::new(RHO, NU, c),
    );
    let fa = [((0, SEL), K::ONE), ((1, SEL), K::t(1 << 5))];
    let mut fb: Vec<((usize, usize), K)> = Vec::new();
    let mut fc: Vec<((usize, usize), K)> = Vec::new();
    for i in 0..4 {
        for r in 0..2 {
            fb.push(((r, XC + i), K::from_u128(1 << i)));
        }
        fc.push(((0, YC + i), K::from_u128(1 << i)));
        fc.push(((1, YC + i), K::from_u128(1 << (5 + i))));
    }
    let fld = R1CS::new(
        RelationField::K,
        RHO,
        NU,
        SparseMatrix::new(RHO, NU, fa),
        SparseMatrix::new(RHO, NU, fb),
        SparseMatrix::new(RHO, NU, fc),
    );
    vec![bin, fld]
}

pub fn segments() -> Vec<Segment> {
    vec![
        Segment {
            seg_id: SEG_IN,
            kind: SegmentKind::Virtual,
            log_cols: 2,
            block: IN >> 2,
        },
        Segment {
            seg_id: SEG_OUT,
            kind: SegmentKind::Virtual,
            log_cols: 2,
            block: OUT >> 2,
        },
        Segment {
            seg_id: SEG_A,
            kind: SegmentKind::Direct,
            log_cols: 2,
            block: A >> 2,
        },
        Segment {
            seg_id: SEG_CARRY,
            kind: SegmentKind::Direct,
            log_cols: 2,
            block: CARRY >> 2,
        },
        Segment {
            seg_id: SEG_X,
            kind: SegmentKind::Direct,
            log_cols: 2,
            block: XC >> 2,
        },
        Segment {
            seg_id: SEG_Y,
            kind: SegmentKind::Direct,
            log_cols: 2,
            block: YC >> 2,
        },
        Segment {
            seg_id: SEG_SEL,
            kind: SegmentKind::Direct,
            log_cols: 0,
            block: SEL,
        },
        Segment {
            seg_id: SEG_PAD,
            kind: SegmentKind::Pad,
            log_cols: 2,
            block: 7,
        },
    ]
}

/// Returns `(W, X, cross)` with honest data (Python `toy_cpu.witness`).
pub fn witness(rng: &mut Rng, q: usize, init: u32) -> (Vec<Vec<bool>>, Vec<Vec<K>>, CrossStep) {
    let mut w: Vec<Vec<bool>> = Vec::new();
    let mut acc = init;
    for _ in 0..q {
        let mut row = vec![false; 1 << (NU - 1)];
        let a = rng.bits_u32(4);
        let mut c = false;
        for i in 0..4 {
            let (ib, ab) = ((acc >> i) & 1 == 1, (a >> i) & 1 == 1);
            row[IN + i] = ib;
            row[A + i] = ab;
            row[CARRY + i] = c;
            row[OUT + i] = ib ^ ab ^ c;
            c = (ib && ab) || (ib && c) || (ab && c);
        }
        let (sel, x) = (rng.bit(), rng.bits_u32(4));
        row[SEL] = sel;
        for i in 0..4 {
            row[XC + i] = (x >> i) & 1 == 1;
            row[YC + i] = sel && ((x >> i) & 1 == 1);
        }
        acc = (acc + a) & 15;
        w.push(row);
    }
    let x: Vec<Vec<K>> = vec![Vec::new(); q];
    let bits4 = |v: u32| -> Vec<bool> { (0..4).map(|i| (v >> i) & 1 == 1).collect() };
    let cross = CrossStep {
        in_id: SEG_IN,
        out_id: SEG_OUT,
        init: bits4(init),
        fin: bits4(acc),
    };
    (w, x, cross)
}
