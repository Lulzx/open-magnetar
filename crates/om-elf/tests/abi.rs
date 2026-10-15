//! Port of `reference/tests/test_abi.py` (plus digest known answers
//! computed from the Python reference).

use std::collections::BTreeMap;

use om_elf::{
    AbiError, Hasher, Params, RAM_BASE, build_m0, decode_region, encode_region,
    expected_output_mle_eval, extract_output, extract_output_slice, input_words, memory_map,
    output_region_bits, output_region_words, program_digest,
};
use om_field::K;

const P: Params = Params {
    ram_log_words: 12,
    input_log_words: 5,
    output_log_words: 3,
    max_code_words: 1 << 20,
    hash_profile: Hasher::Sha256,
};

fn hex(d: &[u8]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

// Python's tests use random.Random(1); the roundtrip property does not
// depend on the exact bytes, so a deterministic LCG stands in.
fn det_bytes(n: usize, seed: u64) -> Vec<u8> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (s >> 33) as u8
        })
        .collect()
}

#[test]
fn memory_map_alignment() {
    for (a, i, o) in [(12, 5, 3), (12, 3, 5), (10, 4, 4), (20, 12, 8)] {
        let m = memory_map(&Params::new(a, i, o)).unwrap();
        assert_eq!(m.input_base % (1 << i), 0);
        assert_eq!(m.output_base % (1 << o), 0);
        assert!(m.input_base + m.input_words <= m.output_base + (1 << i.max(o)));
        assert!(m.output_base + m.output_words <= m.ram_words);
        assert!(
            m.output_base
                >= if i >= o {
                    m.input_base + m.input_words
                } else {
                    m.input_base
                }
        );
        assert_eq!(m.stack_top_addr, RAM_BASE + 8 * m.input_base as u64);
    }
    assert_eq!(
        Params::new(6, 6, 3).validate(),
        Err(AbiError::IoWindowTooLarge)
    );
}

#[test]
fn validate_edges() {
    assert_eq!(
        Params::new(12, 0, 3).validate(),
        Err(AbiError::IoLogWordsTooSmall)
    );
    assert_eq!(Params::new(41, 1, 1).validate(), Err(AbiError::RamTooLarge));
    let mut p = Params::new(12, 3, 3);
    p.max_code_words = 0;
    assert_eq!(p.validate(), Err(AbiError::MaxCodeWordsTooSmall));
    assert!(Params::default().validate().is_ok());
    // memory_map validates first, as in Python.
    assert_eq!(
        memory_map(&Params::new(6, 6, 3)),
        Err(AbiError::IoWindowTooLarge)
    );
}

#[test]
fn roundtrip() {
    for n in [0, 1, 7, 8, 9, 100, 8 * 31] {
        let d = det_bytes(n, 1);
        let w = encode_region(&d, 5).unwrap();
        assert_eq!(w.len(), 32);
        assert_eq!(w[0], n as u64);
        assert_eq!(decode_region(&w, 5).unwrap(), d);
    }
    assert_eq!(
        encode_region(&vec![0u8; 8 * 31 + 1], 5),
        Err(AbiError::RegionTooSmall)
    );
}

#[test]
fn noncanonical_rejected() {
    let mut w = encode_region(b"abc", 3).unwrap();
    w[1] |= 1 << 40;
    assert_eq!(decode_region(&w, 3), Err(AbiError::NonCanonicalRegion));
    let mut w = encode_region(b"abc", 3).unwrap();
    w[5] = 1;
    assert_eq!(decode_region(&w, 3), Err(AbiError::NonCanonicalRegion));
}

#[test]
fn decode_region_edges() {
    assert_eq!(decode_region(&[0u64; 4], 3), Err(AbiError::WrongRegionSize));
    let mut w = vec![0u64; 8];
    w[0] = 57; // 1 + ceil(57/8) = 9 > 8
    assert_eq!(
        decode_region(&w, 3),
        Err(AbiError::DeclaredLengthExceedsRegion)
    );
    w[0] = u64::MAX; // must not overflow the ceil computation
    assert_eq!(
        decode_region(&w, 3),
        Err(AbiError::DeclaredLengthExceedsRegion)
    );
}

#[test]
fn input_and_output_via_ram() {
    let mm = memory_map(&P).unwrap();
    let m0 = build_m0(&BTreeMap::from([(3, 7)]), b"hello world", &P).unwrap();
    assert_eq!(m0[&3], 7);
    assert_eq!(m0[&mm.input_base], 11);
    assert_eq!(m0[&(mm.input_base + 1)], u64::from_le_bytes(*b"hello wo"));
    assert_eq!(input_words(b"", &P).unwrap(), BTreeMap::new());

    let ram = BTreeMap::from([
        (mm.output_base, 3),
        (mm.output_base + 1, 0x63_62_61), // "abc" little-endian
    ]);
    assert_eq!(extract_output(&ram, &P).unwrap(), b"abc");

    assert_eq!(
        build_m0(&BTreeMap::from([(mm.input_base, 1)]), b"", &P),
        Err(AbiError::ProgramDataOutsideRam)
    );
}

#[test]
fn output_via_dense_ram() {
    let mm = memory_map(&P).unwrap();
    let mut ram = vec![0u64; mm.ram_words];
    ram[mm.output_base] = 5;
    ram[mm.output_base + 1] = u64::from_le_bytes(*b"hello\0\0\0");
    let words = output_region_words(
        &BTreeMap::from([
            (mm.output_base, 5),
            (mm.output_base + 1, ram[mm.output_base + 1]),
        ]),
        &P,
    )
    .unwrap();
    assert_eq!(words[0], 5);
    assert_eq!(words.len(), 8);
    assert_eq!(extract_output_slice(&ram, &P).unwrap(), b"hello");
}

#[test]
fn digest_sensitivity() {
    let c = BTreeMap::from([(0x1000_0000, 0x73)]);
    let base = program_digest(&c, 0x1000_0000, &BTreeMap::from([(1, 2)]), &P);
    assert_ne!(
        base,
        program_digest(
            &BTreeMap::from([(0x1000_0000, 0x13)]),
            0x1000_0000,
            &BTreeMap::from([(1, 2)]),
            &P
        )
    );
    assert_ne!(
        base,
        program_digest(&c, 0x1000_0000, &BTreeMap::from([(1, 3)]), &P)
    );
    assert_eq!(
        base,
        program_digest(&c, 0x1000_0000, &BTreeMap::from([(1, 2), (5, 0)]), &P)
    );
}

#[test]
fn digest_known_answers() {
    // Computed with reference/openmagnetar/abi.py (Python oracle).
    let code = BTreeMap::from([(0x1000_0000, 0x73)]);
    let ram = BTreeMap::from([(1, 2)]);
    assert_eq!(
        hex(&program_digest(&code, 0x1000_0000, &ram, &P)),
        "92af9566395d8c149ade68fe256862bd697cc85ae68ce5fff366fefb0002b830"
    );
    let mut p3 = P;
    p3.hash_profile = Hasher::Sha3_256;
    assert_eq!(
        hex(&program_digest(&code, 0x1000_0000, &ram, &p3)),
        "7f619ce5c6cf1207241e72963cf70eda5f547ab746c2f9996271bc9dad5dbc97"
    );
    // 14.3: sha384 profile digests with SHA-384, truncated to 32 bytes.
    let mut p384 = P;
    p384.hash_profile = Hasher::Sha384;
    assert_eq!(
        hex(&program_digest(&code, 0x1000_0000, &ram, &p384)),
        "a0b5c2bc971c9554763bdf2dfd00b706d5262f1bb0646a4a7f2e291f9c345533"
    );
}

#[test]
fn output_mle() {
    let out = b"\x01\x02\x03";
    let bits = output_region_bits(out, &P).unwrap();
    assert_eq!(bits.len(), 64 * 8);
    // At a Boolean point the MLE equals the table entry.
    for idx in [0usize, 64, 64 + 8, 64 + 9, 200] {
        let pt: Vec<K> = (0..9)
            .map(|i| if (idx >> i) & 1 == 1 { K::ONE } else { K::ZERO })
            .collect();
        assert_eq!(
            expected_output_mle_eval(out, &P, &pt).unwrap(),
            K::from_bit(bits[idx])
        );
    }
    // Independent oracle at a non-Boolean point: sum_b eq(r, b) * bit(b).
    let r: Vec<K> = (0..9).map(|i| K::t(0x9e37 + 7919 * i)).collect();
    let mut expect = K::ZERO;
    for (idx, &b) in bits.iter().enumerate() {
        if b {
            let bp: Vec<K> = (0..9).map(|i| K::from_bit((idx >> i) & 1 == 1)).collect();
            expect += om_sumcheck::eq_eval(&r, &bp);
        }
    }
    assert_eq!(expected_output_mle_eval(out, &P, &r).unwrap(), expect);
    assert_eq!(
        expected_output_mle_eval(out, &P, &r[..8]),
        Err(AbiError::WrongPointLength)
    );
}
