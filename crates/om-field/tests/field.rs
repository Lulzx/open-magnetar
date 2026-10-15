//! Ports of `reference/tests/test_field.py` plus the known-answer values
//! of `docs/spec/01-fields.md` / CONVENTIONS C1. Exact expected values
//! below were produced by the Python reference `openmagnetar.field.K`.

use om_field::K;

/// Deterministic splitmix64 stream of field elements (no `rand` crate).
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
        K::from_u128(u128::from(self.next_u64()) | (u128::from(self.next_u64()) << 64))
    }
}

// ---- ports of test_field.py ----

#[test]
fn axioms() {
    // Python: distributivity, associativity, a + a = 0, a * a.inv() = 1.
    let mut rng = Rng(1);
    for _ in 0..200 {
        let (a, b, c) = (rng.next_k(), rng.next_k(), rng.next_k());
        assert_eq!(a * (b + c), a * b + a * c);
        assert_eq!((a * b) * c, a * (b * c));
        assert_eq!(a + a, K::ZERO);
        if !a.is_zero() {
            assert_eq!(a * a.inverse(), K::ONE);
            assert_eq!(a.inv(), Some(a.inverse()));
        }
    }
}

#[test]
fn commutativity_and_char2() {
    let mut rng = Rng(42);
    for _ in 0..200 {
        let (a, b) = (rng.next_k(), rng.next_k());
        assert_eq!(a * b, b * a);
        assert_eq!(a + b, b + a);
        assert_eq!(a - b, a + b);
        assert_eq!(-a, a);
        // Frobenius linearity: (a + b)^2 = a^2 + b^2.
        assert_eq!((a + b).square(), a.square() + b.square());
    }
}

#[test]
fn modulus() {
    // Python: X^127 * X = X^128 = X^7 + X^2 + X + 1 = 0x87.
    let x127 = K::from_u128(1 << 127);
    assert_eq!(x127 * K::X, K::from_u128(0x87));
    assert_eq!(K::X.pow(128), K::from_u128(0x87));
    assert_eq!(K::X.pow(127), x127);
}

#[test]
fn frobenius_on_bits() {
    for b in [K::ZERO, K::ONE] {
        assert_eq!(b.square(), b);
    }
}

#[test]
fn encoding() {
    // Python: K.X.to_bytes() == bytes([2]) + bytes(15).
    let mut expected = [0u8; 16];
    expected[0] = 2;
    assert_eq!(K::X.to_bytes(), expected);
    // Python: from_hex(hex) roundtrips.
    let mut rng = Rng(3);
    for _ in 0..64 {
        let a = rng.next_k();
        assert_eq!(K::from_hex(&a.to_hex()), Some(a));
        assert_eq!(K::from_bytes(&a.to_bytes()), a);
        assert_eq!(a.to_string(), a.to_hex());
        assert_eq!(a.to_string().parse::<K>(), Ok(a));
    }
    // Python: K.pack([0, 1, 1]) == K(6).
    assert_eq!(K::pack(&[false, true, true]), K::from_u128(6));
}

#[test]
fn fermat() {
    // Python: a ** (1 << 128) == a.
    let mut rng = Rng(2);
    for _ in 0..32 {
        let a = rng.next_k();
        assert_eq!(a.pow_limbs(&[0, 0, 1]), a);
        // The same fact as 128 iterated squarings.
        let mut b = a;
        for _ in 0..128 {
            b = b.square();
        }
        assert_eq!(b, a);
        // a^(2^128 - 1) = 1 for a != 0, i.e. a * a^(2^128 - 2) = 1.
        if !a.is_zero() {
            assert_eq!(a.pow(u128::MAX), K::ONE);
        }
    }
}

// ---- known-answer tests (values from the Python reference) ----

#[test]
fn multiplication_kats() {
    let kats: &[(u128, u128, u128)] = &[
        (0, 0, 0),
        (1, u128::MAX, u128::MAX),
        (2, 2, 4),
        (3, 7, 9),
        (0x87, 0x87, 0x4015),
        (1 << 127, 2, 0x87),
        (
            1 << 127,
            1 << 127,
            0xc000_0000_0000_0000_0000_0000_0000_1067,
        ),
        (
            0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
            0x0f0e_0d0c_0b0a_0908_0706_0504_0302_0100,
            0x00a0_9f13_a99b_362b_843f_ed5b_e28f_8be8,
        ),
        (
            u128::MAX,
            u128::MAX,
            0x5555_5555_5555_5555_5555_5555_5555_402f,
        ),
        (
            1 << 127,
            (1 << 127) | 3,
            0x4000_0000_0000_0000_0000_0000_0000_10e0,
        ),
    ];
    for &(a, b, expect) in kats {
        assert_eq!(
            (K::from_u128(a) * K::from_u128(b)).value(),
            expect,
            "a={a:#x} b={b:#x}"
        );
    }
}

#[test]
fn inverse_and_square_kats() {
    // (a, a^-1, a^2) from the Python reference.
    let kats: &[(u128, u128, u128)] = &[
        (1, 1, 1),
        (2, 0x8000_0000_0000_0000_0000_0000_0000_0043, 4),
        (3, 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff82, 5),
        (0x87, 0x5b02_1cae_93f7_8d45_b021_cae9_3f78_d477, 0x4015),
        (
            0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
            0xac20_a8a9_f088_c918_e7a4_a93e_6b40_984a,
            0x55d1_4fc3_3db9_278a_f470_ee62_9c18_862b,
        ),
    ];
    for &(a, inv, sq) in kats {
        let a = K::from_u128(a);
        assert_eq!(a.inv().map(K::value), Some(inv));
        assert_eq!(a.inverse().value(), inv);
        assert_eq!(a.square().value(), sq);
    }
    assert_eq!(K::ZERO.inv(), None);
}

#[test]
#[should_panic(expected = "inverse of zero")]
fn inverse_of_zero_panics() {
    let _ = K::ZERO.inverse();
}

#[test]
fn hex_kats() {
    // Hex is the little-endian byte order (CONVENTIONS C8), so it reads
    // as the byte-reversal of the integer's hex digits.
    assert_eq!(K::ZERO.to_hex(), "00000000000000000000000000000000");
    assert_eq!(K::ONE.to_hex(), "01000000000000000000000000000000");
    assert_eq!(K::X.to_hex(), "02000000000000000000000000000000");
    assert_eq!(
        K::from_u128(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210).to_hex(),
        "1032547698badcfeefcdab8967452301"
    );
    assert_eq!(
        K::from_hex("1032547698badcfeefcdab8967452301"),
        Some(K::from_u128(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210))
    );
    // Uppercase accepted (Python bytes.fromhex behavior).
    assert_eq!(
        K::from_hex("1032547698BADCFEEFCDAB8967452301"),
        Some(K::from_u128(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210))
    );
    // Wrong lengths and non-hex rejected.
    assert_eq!(K::from_hex(""), None);
    assert_eq!(K::from_hex("00"), None);
    assert_eq!(K::from_hex("zz000000000000000000000000000000"), None);
    // Debug mirrors the Python repr (integer-value hex).
    assert_eq!(
        format!("{:?}", K::X),
        "K(0x00000000000000000000000000000002)"
    );
}

#[test]
fn byte_slice_lengths() {
    assert_eq!(K::from_byte_slice(&[0u8; 15]), None);
    assert_eq!(K::from_byte_slice(&[0u8; 17]), None);
    assert_eq!(
        K::from_byte_slice(&[2u8; 16]),
        Some(K::from_bytes(&[2u8; 16]))
    );
    // Every 16-byte string is valid (spec 01 §1.2).
    let mut rng = Rng(9);
    for _ in 0..64 {
        let a = rng.next_k();
        assert_eq!(K::from_byte_slice(&a.to_bytes()), Some(a));
    }
}

#[test]
fn pack_unpack() {
    assert_eq!(K::pack(&[]), K::ZERO);
    assert_eq!(K::pack(&[true]), K::ONE);
    assert_eq!(K::pack(&[false, true]), K::X);
    // Bit j is the coefficient of X^j: pack then unpack roundtrips, and
    // unpack of X^j has exactly bit j set.
    for j in [0usize, 1, 2, 7, 63, 64, 127] {
        let bits = K::from_u128(1u128 << j).unpack();
        assert_eq!(bits.iter().filter(|&&b| b).count(), 1);
        assert!(bits[j]);
    }
    let mut rng = Rng(5);
    for _ in 0..128 {
        let a = rng.next_k();
        assert_eq!(K::pack(&a.unpack()), a);
        // Packed bytes are byte-identical to the encoding (spec 01 §1.2).
        let bits = a.unpack();
        for i in 0..16 {
            let mut byte = 0u8;
            for j in 0..8 {
                byte |= u8::from(bits[8 * i + j]) << j;
            }
            assert_eq!(byte, a.to_bytes()[i]);
        }
    }
}

#[test]
#[should_panic(expected = "at most 128 bits")]
fn pack_too_many_bits_panics() {
    let _ = K::pack(&[true; 129]);
}

#[test]
fn small_integer_points() {
    // C1: t_0 = 0, t_1 = 1, t_2 = X, t_3 = X + 1, t_4 = X^2.
    assert_eq!(K::t(0), K::ZERO);
    assert_eq!(K::t(1), K::ONE);
    assert_eq!(K::t(2), K::X);
    assert_eq!(K::t(3), K::X + K::ONE);
    assert_eq!(K::t(4), K::X * K::X);
    // C1: t_k + t_j = t_{k xor j}.
    let mut rng = Rng(11);
    for _ in 0..100 {
        let (k, j) = (rng.next_k().value(), rng.next_k().value());
        assert_eq!(K::t(k) + K::t(j), K::t(k ^ j));
    }
}

#[test]
fn pow_basics() {
    assert_eq!(K::ZERO.pow(0), K::ONE); // 0^0 = 1, as in Python
    assert_eq!(K::ZERO.pow(5), K::ZERO);
    assert_eq!(K::X.pow(0), K::ONE);
    assert_eq!(K::X.pow(1), K::X);
    assert_eq!(K::t(3).pow(2), K::from_u128(5)); // (X+1)^2 = X^2 + 1
    let mut rng = Rng(13);
    for _ in 0..32 {
        let a = rng.next_k();
        assert_eq!(a.pow(2), a.square());
        assert_eq!(a.pow(3), a * a * a);
        assert_eq!(a.pow_limbs(&[]), K::ONE);
        assert_eq!(a.pow_limbs(&[3]), a.pow(3));
        assert_eq!(a.pow_limbs(&[0, 1]), a.pow_limbs(&[0, 1, 0]));
    }
}

#[test]
fn division_and_bit_products() {
    let mut rng = Rng(17);
    for _ in 0..100 {
        let (a, b) = (rng.next_k(), rng.next_k());
        if !b.is_zero() {
            assert_eq!((a / b) * b, a);
        }
        // B embedding and B × K products (spec 01 §1.5).
        assert_eq!(a.mul_bit(true), a);
        assert_eq!(a.mul_bit(false), K::ZERO);
        assert_eq!(K::from_bit(true), K::ONE);
        assert_eq!(K::from(false), K::ZERO);
        assert_eq!(a * K::from_bit(true), a.mul_bit(true));
    }
}
