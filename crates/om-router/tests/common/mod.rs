//! Shared helpers for the om-router integration tests.
#![allow(dead_code)]

use om_field::K;

/// Deterministic splitmix64 stream (no `rand` crate), as in the
/// om-memcheck tests. The Python tests use `random.Random(seed)`; the
/// Rust ports keep the same shapes and assertions with this stream
/// (byte-exact randomness is pinned by the vectors instead).
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
    /// True with probability about `num / den`.
    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.next_u64() % den < num
    }
    /// Uniform in `[0, n)`.
    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
    /// `getrandbits(bits)` for `bits <= 64`.
    pub fn word(&mut self, bits: u32) -> u64 {
        if bits == 64 {
            self.next_u64()
        } else {
            self.next_u64() & ((1u64 << bits) - 1)
        }
    }
}
