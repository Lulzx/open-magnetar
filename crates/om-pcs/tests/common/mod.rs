//! Shared deterministic RNG for the om-pcs integration tests.
#![allow(dead_code)]

use om_field::K;

/// Deterministic splitmix64 stream (no `rand` crate), as in om-field tests.
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
    pub fn bits(&mut self, n: usize) -> Vec<bool> {
        (0..n).map(|_| self.bit()).collect()
    }
}
