//! The binary field `K = GF(2^128)` of Open Magnetar.
//!
//! Normative references: `docs/spec/CONVENTIONS.md` C1 and
//! `docs/spec/01-fields.md`. Behavioral reference: class `K` in
//! `reference/openmagnetar/field.py`.
//!
//! `K = GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)`. An element is identified
//! with the 128-bit unsigned integer whose bit `i` is the coefficient of
//! `X^i` — the plain polynomial basis, **not** GHASH's bit-reflected
//! convention. Addition is XOR (so subtraction is addition and negation is
//! the identity); multiplication is carry-less polynomial multiplication
//! followed by reduction modulo `X^128 + X^7 + X^2 + X + 1`.
//!
//! Encoding (C1/C8, spec 01 §1.2): 16 bytes, little-endian — byte 0 holds
//! bits 0..7. Every 16-byte string is a valid canonical encoding. The
//! textual form (used by [`Display`](core::fmt::Display), [`K::to_hex`],
//! and test vectors) is the 32-character lowercase hex of those
//! little-endian bytes. [`Debug`](core::fmt::Debug) instead mirrors the
//! Python `repr`, `K(0x…)`, printed from the integer value.

// In characteristic 2, addition and subtraction genuinely are XOR and
// division genuinely is multiplication by the inverse.
#![allow(clippy::suspicious_arithmetic_impl)]
#![allow(clippy::suspicious_op_assign_impl)]

use core::fmt;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use core::str::FromStr;

/// `X^128 mod m(X) = X^7 + X^2 + X + 1`, the low terms of the modulus
/// `m(X) = X^128 + X^7 + X^2 + X + 1` (as an integer, `(1 << 128) | 0x87`).
const REDUCTION: u128 = 0x87;

/// An element of `K = GF(2^128)`, stored as its integer value (bit `i` =
/// coefficient of `X^i`).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct K(u128);

impl K {
    /// The zero element, `0`.
    pub const ZERO: K = K(0);
    /// The one element, `1` (also the embedding of `1 ∈ GF(2)`).
    pub const ONE: K = K(1);
    /// The element `X` (integer value 2).
    pub const X: K = K(2);

    /// The element with integer value `v`. Every `u128` is in range, so
    /// this never fails (the Python `K(v)` range check is vacuous here).
    #[inline(always)]
    pub const fn from_u128(v: u128) -> K {
        K(v)
    }

    /// The field point `t_k`: the element with integer value `k`
    /// (CONVENTIONS C1). So `t(0) = 0`, `t(1) = 1`, `t(2) = X`,
    /// `t(3) = X + 1`.
    #[inline(always)]
    pub const fn t(k: u128) -> K {
        K(k)
    }

    /// The integer value of this element (bit `i` = coefficient of `X^i`).
    #[inline(always)]
    pub const fn value(self) -> u128 {
        self.0
    }

    /// The embedding of a bit of `B = GF(2)`: `false ↦ 0`, `true ↦ 1`.
    #[inline(always)]
    pub const fn from_bit(b: bool) -> K {
        K(b as u128)
    }

    /// Whether this element is zero.
    #[inline(always)]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    /// Whether this element is one.
    #[inline(always)]
    pub const fn is_one(self) -> bool {
        self.0 == 1
    }

    // ---- byte / hex encoding (spec 01 §1.2, CONVENTIONS C8) ----

    /// The canonical 16-byte little-endian encoding: byte `i` holds
    /// integer bits `8i..8i+7`, so byte 0 holds `X^0..X^7`.
    #[inline(always)]
    pub fn to_bytes(self) -> [u8; 16] {
        self.0.to_le_bytes()
    }

    /// Decode a canonical 16-byte little-endian encoding. Every 16-byte
    /// string is valid.
    #[inline(always)]
    pub fn from_bytes(b: &[u8; 16]) -> K {
        K(u128::from_le_bytes(*b))
    }

    /// Decode from a byte slice, rejecting any length other than 16
    /// (mirrors Python `K.from_bytes`, which raises on other lengths).
    #[inline]
    pub fn from_byte_slice(b: &[u8]) -> Option<K> {
        let arr: &[u8; 16] = b.try_into().ok()?;
        Some(K::from_bytes(arr))
    }

    /// The 32-character lowercase hex of the little-endian byte encoding
    /// (the test-vector form of CONVENTIONS C8; Python `K.hex`).
    pub fn to_hex(self) -> String {
        let mut s = String::with_capacity(32);
        for byte in self.to_bytes() {
            s.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble < 16"));
            s.push(char::from_digit(u32::from(byte & 0xf), 16).expect("nibble < 16"));
        }
        s
    }

    /// Parse the 32-character hex form produced by [`K::to_hex`]
    /// (upper- or lowercase digits accepted, as in Python
    /// `bytes.fromhex`). Returns `None` unless the input is exactly 32
    /// hex characters.
    pub fn from_hex(s: &str) -> Option<K> {
        let bytes = s.as_bytes();
        if bytes.len() != 32 {
            return None;
        }
        let mut out = [0u8; 16];
        for (i, byte) in out.iter_mut().enumerate() {
            let hi = hex_val(bytes[2 * i])?;
            let lo = hex_val(bytes[2 * i + 1])?;
            *byte = (hi << 4) | lo;
        }
        Some(K::from_bytes(&out))
    }

    // ---- packing (spec 01 §1.3) ----

    /// Pack up to 128 bits with basis `β_j = X^j`: bit `j` of the result
    /// is `bits[j]`. Missing high bits are zero, as in Python `K.pack`.
    ///
    /// # Panics
    /// Panics if `bits.len() > 128`.
    pub fn pack(bits: &[bool]) -> K {
        assert!(bits.len() <= 128, "K::pack expects at most 128 bits");
        let mut v = 0u128;
        for (j, &bit) in bits.iter().enumerate() {
            v |= u128::from(bit) << j;
        }
        K(v)
    }

    /// The inverse of [`K::pack`]: entry `j` is the coefficient of `X^j`.
    pub fn unpack(self) -> [bool; 128] {
        let mut out = [false; 128];
        for (j, bit) in out.iter_mut().enumerate() {
            *bit = (self.0 >> j) & 1 == 1;
        }
        out
    }

    // ---- arithmetic ----

    /// The Frobenius map `x ↦ x^2` (Python `K.square`).
    #[inline(always)]
    pub fn square(self) -> K {
        self * self
    }

    /// `self^e` for a `u128` exponent, by square-and-multiply. `0^0 = 1`,
    /// as in Python.
    pub fn pow(self, mut e: u128) -> K {
        let mut r = K::ONE;
        let mut b = self;
        while e != 0 {
            if e & 1 == 1 {
                r *= b;
            }
            b = b.square();
            e >>= 1;
        }
        r
    }

    /// `self^e` for an exponent given as little-endian 64-bit limbs, for
    /// exponents that do not fit in `u128` (e.g. the Fermat exponent
    /// `2^128`, limbs `[0, 0, 1]`). An empty or all-zero exponent gives
    /// `1` (so `0^0 = 1`, as in Python).
    pub fn pow_limbs(self, exp: &[u64]) -> K {
        let mut r = K::ONE;
        // Square-and-multiply from the most significant bit down.
        let mut started = false;
        for &limb in exp.iter().rev() {
            for i in (0..64).rev() {
                if started {
                    r = r.square();
                }
                if (limb >> i) & 1 == 1 {
                    if started {
                        r *= self;
                    } else {
                        r = self;
                        started = true;
                    }
                }
            }
        }
        r
    }

    /// The multiplicative inverse, or `None` for zero.
    pub fn inv(self) -> Option<K> {
        if self.is_zero() {
            None
        } else {
            // a^(2^128 - 2), as in Python `K.inv`.
            Some(self.pow(u128::MAX - 1))
        }
    }

    /// The multiplicative inverse, panicking on zero. This mirrors Python
    /// `K.inv`, which raises `ZeroDivisionError` on zero; prefer
    /// [`K::inv`] where zero is possible.
    ///
    /// # Panics
    /// Panics if `self` is zero.
    pub fn inverse(self) -> K {
        self.inv().expect("inverse of zero in K")
    }

    /// The product `b · self` for a bit `b ∈ B` (spec 01 §1.5): `self` if
    /// `b` is set, else zero.
    #[inline(always)]
    pub fn mul_bit(self, b: bool) -> K {
        if b { self } else { K::ZERO }
    }

    /// Multiply `self` by `X = K(2)`: `(v << 1) ^ (if v >> 127 != 0 { 0x87 } else { 0 })`.
    #[inline(always)]
    pub const fn mul_x(self) -> K {
        let hi = (self.0 as i128 >> 127) as u128;
        K((self.0 << 1) ^ (hi & REDUCTION))
    }

    /// Multiply `self` by the field point `K::t(k)`, using shift-and-XOR
    /// for small `k <= 7` (the sum-check evaluation points `t_0..t_7`).
    #[inline(always)]
    pub fn mul_t(self, k: u128) -> K {
        match k {
            0 => K::ZERO,
            1 => self,
            2 => self.mul_x(),
            3 => self.mul_x() + self,
            4 => self.mul_x().mul_x(),
            5 => self.mul_x().mul_x() + self,
            6 => {
                let x = self.mul_x();
                x.mul_x() + x
            }
            7 => {
                let x = self.mul_x();
                x.mul_x() + x + self
            }
            _ => self * K::t(k),
        }
    }

    /// Unreduced 128×128 → 256-bit carry-less product `self · rhs` in `GF(2)[X]`.
    /// By linearity of modular reduction over `GF(2)`, a sum of products
    /// `Σ_i a_i * b_i` can be accumulated as `U256` via XOR (`+` / `+=`) and
    /// reduced once with [`U256::reduce`].
    #[inline(always)]
    pub fn clmul(self, rhs: K) -> U256 {
        let (lo, hi) = clmul128(self.0, rhs.0);
        U256(lo, hi)
    }
}

/// An unreduced 256-bit polynomial in `GF(2)[X]` (`lo + hi · X^128`), used to
/// accumulate sums of products before a single modular reduction via [`U256::reduce`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct U256(pub u128, pub u128);

impl U256 {
    /// The zero polynomial.
    pub const ZERO: U256 = U256(0, 0);

    /// Embed a reduced field element `k` as `k + 0 · X^128`.
    #[inline(always)]
    pub const fn from_k(k: K) -> U256 {
        U256(k.0, 0)
    }

    /// Reduce modulo `m(X) = X^128 + X^7 + X^2 + X + 1` into [`K`].
    #[inline(always)]
    pub fn reduce(self) -> K {
        K(reduce(self.0, self.1))
    }
}

impl Add for U256 {
    type Output = U256;
    #[inline(always)]
    fn add(self, rhs: U256) -> U256 {
        U256(self.0 ^ rhs.0, self.1 ^ rhs.1)
    }
}

impl AddAssign for U256 {
    #[inline(always)]
    fn add_assign(&mut self, rhs: U256) {
        self.0 ^= rhs.0;
        self.1 ^= rhs.1;
    }
}

fn hex_val(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

impl From<bool> for K {
    #[inline(always)]
    fn from(b: bool) -> K {
        K::from_bit(b)
    }
}

impl Add for K {
    type Output = K;
    #[inline(always)]
    fn add(self, rhs: K) -> K {
        K(self.0 ^ rhs.0)
    }
}

impl AddAssign for K {
    #[inline(always)]
    fn add_assign(&mut self, rhs: K) {
        self.0 ^= rhs.0;
    }
}

/// Subtraction is addition in characteristic 2.
impl Sub for K {
    type Output = K;
    #[inline(always)]
    fn sub(self, rhs: K) -> K {
        K(self.0 ^ rhs.0)
    }
}

impl SubAssign for K {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: K) {
        self.0 ^= rhs.0;
    }
}

/// Negation is the identity in characteristic 2.
impl Neg for K {
    type Output = K;
    #[inline(always)]
    fn neg(self) -> K {
        self
    }
}

impl Mul for K {
    type Output = K;
    #[inline(always)]
    fn mul(self, rhs: K) -> K {
        mul(self, rhs)
    }
}

impl MulAssign for K {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: K) {
        *self = *self * rhs;
    }
}

/// Division multiplies by the inverse (Python `__truediv__`).
///
/// # Panics
/// Panics if `rhs` is zero.
impl Div for K {
    type Output = K;
    fn div(self, rhs: K) -> K {
        self * rhs.inverse()
    }
}

impl DivAssign for K {
    fn div_assign(&mut self, rhs: K) {
        *self = *self / rhs;
    }
}

/// The [`Display`](fmt::Display) form is the vector encoding: 32-char
/// lowercase hex of the little-endian bytes (CONVENTIONS C8).
impl fmt::Display for K {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_hex())
    }
}

/// The [`Debug`](fmt::Debug) form mirrors the Python `repr`:
/// `K(0x…)` with the integer value in hex.
impl fmt::Debug for K {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "K(0x{:032x})", self.0)
    }
}

/// Error returned when parsing a [`K`] from a string that is not exactly
/// 32 hex characters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseKError;

impl fmt::Display for ParseKError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("K hex encoding must be exactly 32 hex characters")
    }
}

impl std::error::Error for ParseKError {}

impl FromStr for K {
    type Err = ParseKError;
    fn from_str(s: &str) -> Result<K, ParseKError> {
        K::from_hex(s).ok_or(ParseKError)
    }
}

// ---- multiplication: carry-less multiply + reduction (spec 01 §1.6) ----

#[inline(always)]
fn clmul128(a: u128, b: u128) -> (u128, u128) {
    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    {
        // SAFETY: `aes` (FEAT_PMULL) is enabled at compile time.
        return unsafe { clmul128_aarch64(a, b) };
    }
    #[cfg(all(target_arch = "aarch64", not(target_feature = "aes")))]
    {
        if std::arch::is_aarch64_feature_detected!("aes") {
            // SAFETY: the `aes` target feature (which includes PMULL) was
            // just detected at runtime on this CPU.
            return unsafe { clmul128_aarch64(a, b) };
        }
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "pclmulqdq"))]
    {
        // SAFETY: PCLMULQDQ is enabled at compile time; SSE2 is part of the
        // x86-64 baseline.
        return unsafe { clmul128_x86_64(a, b) };
    }
    #[cfg(all(target_arch = "x86_64", not(target_feature = "pclmulqdq")))]
    {
        if std::arch::is_x86_feature_detected!("pclmulqdq") {
            // SAFETY: PCLMULQDQ was just detected at runtime on this CPU;
            // SSE2 is part of the x86-64 baseline.
            return unsafe { clmul128_x86_64(a, b) };
        }
    }
    #[allow(unreachable_code)]
    clmul128_portable(a, b)
}

#[inline(always)]
fn mul(a: K, b: K) -> K {
    let (lo, hi) = clmul128(a.0, b.0);
    K(reduce(lo, hi))
}

/// Portable multiplication, always compiled; the reference that the
/// accelerated paths are tested against.
#[cfg(test)]
pub(crate) fn mul_portable(a: K, b: K) -> K {
    let (lo, hi) = clmul128_portable(a.0, b.0);
    K(reduce(lo, hi))
}

/// Carry-less product of two `u64`s as a `u128`, by shift-and-XOR.
fn clmul64_portable(a: u64, b: u64) -> u128 {
    let mut r = 0u128;
    let mut a = u128::from(a);
    let mut b = b;
    while b != 0 {
        if b & 1 == 1 {
            r ^= a;
        }
        a <<= 1;
        b >>= 1;
    }
    r
}

/// Carry-less 128×128 → 256 product as `(lo, hi)`, from four 64×64
/// products computed by `clmul64`.
#[inline(always)]
fn clmul128_with<Fn64: Fn(u64, u64) -> u128>(a: u128, b: u128, clmul64: Fn64) -> (u128, u128) {
    let (a0, a1) = (a as u64, (a >> 64) as u64);
    let (b0, b1) = (b as u64, (b >> 64) as u64);
    let p00 = clmul64(a0, b0);
    let mid = clmul64(a0, b1) ^ clmul64(a1, b0);
    let p11 = clmul64(a1, b1);
    (p00 ^ (mid << 64), p11 ^ (mid >> 64))
}

fn clmul128_portable(a: u128, b: u128) -> (u128, u128) {
    clmul128_with(a, b, clmul64_portable)
}

/// Reduce the 256-bit product `(lo, hi)` modulo `m(X)` by folding `hi`
/// twice with `X^128 ≡ 0x87` (spec 01 §1.6): `lo ^= hi·0x87 (mod 2^128)`,
/// then the at-most-7-bit overflow of that product is folded once more.
#[inline(always)]
fn reduce(lo: u128, hi: u128) -> u128 {
    // hi · 0x87 = hi ^ hi<<1 ^ hi<<2 ^ hi<<7, up to 135 bits.
    let low = hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7);
    let overflow = (hi >> 127) ^ (hi >> 126) ^ (hi >> 121);
    debug_assert_eq!(REDUCTION, 0x87);
    lo ^ low ^ overflow ^ (overflow << 1) ^ (overflow << 2) ^ (overflow << 7)
}

/// AArch64 128×128 → 256 carry-less product using `PMULL` (`vmull_p64`).
///
/// # Safety
/// The caller must ensure the CPU supports the `aes` target feature (FEAT_PMULL).
#[cfg(target_arch = "aarch64")]
#[inline]
#[target_feature(enable = "aes")]
unsafe fn clmul128_aarch64(a: u128, b: u128) -> (u128, u128) {
    use core::arch::aarch64::vmull_p64;
    clmul128_with(a, b, |x, y| vmull_p64(x, y))
}

/// x86-64 128×128 → 256 carry-less product using `PCLMULQDQ`.
///
/// # Safety
/// The caller must ensure the CPU supports PCLMULQDQ and SSE2.
#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "pclmulqdq,sse2")]
unsafe fn clmul128_x86_64(a: u128, b: u128) -> (u128, u128) {
    use core::arch::x86_64::{__m128i, _mm_clmulepi64_si128, _mm_set_epi64x, _mm_storeu_si128};

    let clmul64 = |x: u64, y: u64| {
        let px = _mm_set_epi64x(0, x as i64);
        let py = _mm_set_epi64x(0, y as i64);
        let prod = _mm_clmulepi64_si128::<0x00>(px, py);
        let mut out = [0u64; 2];
        unsafe { _mm_storeu_si128(out.as_mut_ptr().cast::<__m128i>(), prod) };
        u128::from(out[0]) | (u128::from(out[1]) << 64)
    };
    clmul128_with(a, b, clmul64)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Deterministic splitmix64 stream of `u128`s (no `rand` crate).
    struct Rng(u64);

    impl Rng {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }
        fn next_k(&mut self) -> K {
            K(u128::from(self.next_u64()) | (u128::from(self.next_u64()) << 64))
        }
    }

    #[test]
    fn portable_matches_operator() {
        let mut rng = Rng(0x1234_5678);
        for _ in 0..512 {
            let (a, b) = (rng.next_k(), rng.next_k());
            assert_eq!(mul_portable(a, b), a * b);
        }
        // Edge operands, including the reduction-heavy high bits.
        for &v in &[0u128, 1, 2, 0x87, u128::MAX, 1 << 127, (1 << 127) | 3] {
            for &w in &[0u128, 1, 2, 0x87, u128::MAX, 1 << 127] {
                assert_eq!(mul_portable(K(v), K(w)), K(v) * K(w));
            }
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn pmull_matches_portable() {
        if !std::arch::is_aarch64_feature_detected!("aes") {
            return;
        }
        let mut rng = Rng(0xdead_beef);
        for _ in 0..1024 {
            let (a, b) = (rng.next_k(), rng.next_k());
            // SAFETY: `aes` was detected just above.
            let (lo, hi) = unsafe { clmul128_aarch64(a.0, b.0) };
            assert_eq!(K(reduce(lo, hi)), mul_portable(a, b), "a={a:?} b={b:?}");
        }
        for &v in &[0u128, 1, u128::MAX, 1 << 127, 1 << 64, (1 << 64) - 1] {
            for &w in &[0u128, 1, u128::MAX, 1 << 127, 1 << 64] {
                // SAFETY: `aes` was detected just above.
                let (lo, hi) = unsafe { clmul128_aarch64(v, w) };
                assert_eq!(K(reduce(lo, hi)), mul_portable(K(v), K(w)));
            }
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn pclmulqdq_matches_portable() {
        if !std::arch::is_x86_feature_detected!("pclmulqdq") {
            return;
        }
        let mut rng = Rng(0xdead_beef);
        for _ in 0..1024 {
            let (a, b) = (rng.next_k(), rng.next_k());
            // SAFETY: PCLMULQDQ was detected just above.
            let (lo, hi) = unsafe { clmul128_x86_64(a.0, b.0) };
            assert_eq!(K(reduce(lo, hi)), mul_portable(a, b), "a={a:?} b={b:?}");
        }
    }

    #[test]
    fn reduce_matches_python_fold() {
        // The reference reduce: while r >> 128: r = lo ^ h·0x87.
        fn py_reduce(lo: u128, hi: u128) -> u128 {
            // One fold may still overflow; emulate with a 256-bit pair.
            let (mut lo, mut hi) = (lo, hi);
            while hi != 0 {
                let (nlo, nhi) = clmul128_portable(hi, REDUCTION);
                lo ^= nlo;
                hi = nhi;
            }
            lo
        }
        let mut rng = Rng(7);
        for _ in 0..256 {
            let (a, b) = (rng.next_k(), rng.next_k());
            let (lo, hi) = clmul128_portable(a.0, b.0);
            assert_eq!(reduce(lo, hi), py_reduce(lo, hi));
        }
    }

    #[test]
    fn mul_x_and_mul_t_match_mul() {
        let mut rng = Rng(0x4242);
        for _ in 0..512 {
            let a = rng.next_k();
            assert_eq!(a.mul_x(), a * K::X);
            for k in 0..16 {
                assert_eq!(a.mul_t(k), a * K::t(k));
            }
        }
        for &v in &[0u128, 1, 2, 0x87, u128::MAX, 1 << 127, (1 << 127) | 3] {
            let a = K(v);
            assert_eq!(a.mul_x(), a * K::X);
            for k in 0..16 {
                assert_eq!(a.mul_t(k), a * K::t(k));
            }
        }
    }

    #[test]
    fn clmul_unreduced_sum_matches_reduced() {
        let mut rng = Rng(0x9999);
        let mut sum_k = K::ZERO;
        let mut sum_u256 = U256::ZERO;
        for _ in 0..512 {
            let (a, b) = (rng.next_k(), rng.next_k());
            sum_k += a * b;
            sum_u256 += a.clmul(b);
        }
        assert_eq!(sum_u256.reduce(), sum_k);
    }
}
