//! SDK integration tests on the om-prover test Fibonacci program
//! (assembled with the same `common` helper), wrapped once as a code
//! image and once as a minimal in-test ELF (the `om-elf` test
//! builder pattern).

mod common;

use std::collections::BTreeMap;

use common::*;
use om_sdk::{
    AbiParams, Hasher, SdkError, SdkParams, encode_instance, encode_vk, execute, execute_input,
    from_statement_instance, keygen_from_code, keygen_from_elf, prove, prove_input,
    to_statement_instance, verify, verify_bytes,
};

/// Tiny ABI of the reference protocol tests: 16 RAM words, 2-word
/// input/output regions (output words 14/15 = byte offsets 112/120).
fn ap() -> AbiParams {
    AbiParams {
        ram_log_words: 4,
        input_log_words: 1,
        output_log_words: 1,
        max_code_words: 256,
        hash_profile: Hasher::Sha256,
    }
}

fn test_params() -> SdkParams {
    SdkParams::test_profile().with_abi(ap())
}

/// Fibonacci by pairs (Python `fib_program`); output 13, exit 0.
fn fib_program() -> Vec<u32> {
    let mut p = vec![
        addi(1, 0, 1),
        slli(1, 1, 31),
        addi(3, 0, 1),
        addi(4, 0, 3),
        add(2, 2, 3),
        add(3, 3, 2),
        addi(4, 4, -1),
        bne(4, 0, -12),
        addi(5, 0, 8),
        sd(5, 1, 112),
        sd(3, 1, 120),
        addi(10, 0, 0),
    ];
    p.extend(halt());
    p
}

const TEXT: u64 = 0x1000_0000;

/// Minimal ELF64 with one R|X PT_LOAD code segment at `TEXT`
/// (simplified from the `om-elf` tests' `make_elf`).
fn make_elf(instrs: &[u32]) -> Vec<u8> {
    let data: Vec<u8> = instrs.iter().flat_map(|w| w.to_le_bytes()).collect();
    let (ehsize, phsize) = (64u64, 56u64);
    let off = ehsize + phsize;
    let mut e = b"\x7fELF".to_vec();
    e.extend_from_slice(&[2, 1, 1, 0]); // 64-bit, LE, current, SysV
    e.extend_from_slice(&[0u8; 8]);
    e.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    e.extend_from_slice(&243u16.to_le_bytes()); // EM_RISCV
    e.extend_from_slice(&1u32.to_le_bytes());
    e.extend_from_slice(&TEXT.to_le_bytes()); // entry
    e.extend_from_slice(&ehsize.to_le_bytes()); // phoff
    e.extend_from_slice(&0u64.to_le_bytes()); // shoff
    e.extend_from_slice(&0u32.to_le_bytes()); // flags
    e.extend_from_slice(&64u16.to_le_bytes());
    e.extend_from_slice(&56u16.to_le_bytes());
    e.extend_from_slice(&1u16.to_le_bytes()); // phnum
    e.extend_from_slice(&64u16.to_le_bytes());
    e.extend_from_slice(&0u16.to_le_bytes());
    e.extend_from_slice(&0u16.to_le_bytes());
    // One PT_LOAD program header (R|X = 5).
    e.extend_from_slice(&1u32.to_le_bytes());
    e.extend_from_slice(&5u32.to_le_bytes());
    e.extend_from_slice(&off.to_le_bytes());
    e.extend_from_slice(&TEXT.to_le_bytes());
    e.extend_from_slice(&TEXT.to_le_bytes());
    e.extend_from_slice(&(data.len() as u64).to_le_bytes());
    e.extend_from_slice(&(data.len() as u64).to_le_bytes());
    e.extend_from_slice(&8u64.to_le_bytes());
    e.extend_from_slice(&data);
    e
}

#[test]
fn keygen_from_code_prove_verify() {
    let (code, entry) = program(&fib_program());
    let vk = keygen_from_code(&code, entry, &BTreeMap::new(), &test_params()).expect("keygen");

    let (output, exit_code) = execute_input(&vk, b"").expect("execute");
    assert_eq!(exit_code, 0);
    assert_eq!(u64::from_le_bytes(output[..8].try_into().unwrap()), 13);

    let (instance, proof_blob) = prove_input(&vk, b"").expect("prove");
    assert_eq!(instance.t, 32);
    assert_eq!(instance.output, output);
    verify(&vk, &instance, &proof_blob).expect("verify accepts");
    verify_bytes(&encode_vk(&vk), &encode_instance(&instance), &proof_blob)
        .expect("verify_bytes accepts");

    // The section-14.3 statement form is the same claim with the
    // program digest in place of T, and round-trips.
    let statement = to_statement_instance(&vk, &instance);
    assert_eq!(statement.program_digest, vk.program_digest);
    assert_eq!(from_statement_instance(&statement, instance.t), instance);
}

#[test]
fn keygen_from_elf_flow_and_rejections() {
    let elf = make_elf(&fib_program());
    let vk = keygen_from_elf(&elf, &test_params()).expect("keygen");

    let (output, exit_code) = execute(&vk, &elf, b"").expect("execute");
    assert_eq!(exit_code, 0);
    assert_eq!(u64::from_le_bytes(output[..8].try_into().unwrap()), 13);

    let (instance, proof_blob) = prove(&vk, &elf, b"").expect("prove");
    verify(&vk, &instance, &proof_blob).expect("verify accepts");

    // Wrong output rejects.
    let mut bad = instance.clone();
    bad.output[0] ^= 1;
    assert!(
        verify(&vk, &bad, &proof_blob).is_err(),
        "tampered output must reject"
    );
    // Wrong input rejects (the input is part of the statement).
    let mut bad = instance.clone();
    bad.input = vec![1];
    assert!(
        verify(&vk, &bad, &proof_blob).is_err(),
        "tampered input must reject"
    );
    // A flipped proof byte rejects.
    let mut bad_proof = proof_blob.clone();
    let n = bad_proof.len();
    bad_proof[n - 1] ^= 1;
    assert!(
        verify(&vk, &instance, &bad_proof).is_err(),
        "tampered proof must reject"
    );

    // Proving a different ELF against this vk is a clean error.
    let other = make_elf(&halt());
    assert!(matches!(
        prove(&vk, &other, b""),
        Err(SdkError::ProgramMismatch)
    ));
    assert!(matches!(
        execute(&vk, &other, b""),
        Err(SdkError::ProgramMismatch)
    ));
}

#[test]
fn malformed_inputs_are_errors_not_panics() {
    assert!(keygen_from_elf(b"not an elf", &test_params()).is_err());
    assert!(keygen_from_elf(&[], &test_params()).is_err());
    assert!(verify_bytes(b"", b"", b"").is_err());
    assert!(verify_bytes(b"OMVK", b"OMIN", b"OMPF").is_err());
    // A test profile with pcs_t = 0 is a key error, not a panic.
    let mut bad = test_params();
    bad.pcs_t = 0;
    let (code, entry) = program(&fib_program());
    assert!(keygen_from_code(&code, entry, &BTreeMap::new(), &bad).is_err());
}

#[test]
fn provable120_prove_verify() {
    let params = SdkParams::default().with_abi(ap());
    let (code, entry) = program(&fib_program());
    let vk = keygen_from_code(&code, entry, &BTreeMap::new(), &params).expect("keygen");
    let (instance, proof_blob) = prove_input(&vk, b"").expect("prove");
    verify(&vk, &instance, &proof_blob).expect("verify accepts");
}

#[test]
fn hash_profiles_sha384_and_sha3_256_prove_verify() {
    let (code, entry) = program(&fib_program());
    for hash_profile in [Hasher::Sha384, Hasher::Sha3_256] {
        let mut abi = ap();
        abi.hash_profile = hash_profile;
        let params = SdkParams::test_profile().with_abi(abi);
        let vk = keygen_from_code(&code, entry, &BTreeMap::new(), &params).expect("keygen");
        let (instance, proof_blob) = prove_input(&vk, b"").expect("prove");
        verify(&vk, &instance, &proof_blob).expect("verify accepts");
        verify_bytes(&encode_vk(&vk), &encode_instance(&instance), &proof_blob)
            .expect("verify_bytes accepts");
    }
}
