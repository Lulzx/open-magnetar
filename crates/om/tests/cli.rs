//! CLI integration tests: spawn the real `om` binary and run the
//! keygen -> prove -> verify roundtrip on temp files (fib guest
//! ELF, test PCS profile), plus the reject and `run` paths.

mod common;

use std::path::PathBuf;
use std::process::{Command, Output};

use common::*;

/// Fibonacci by pairs (Python `fib_program`); output 13, exit 0,
/// for A=4, I=O=1 (output region at byte offsets 112/120).
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
    e.extend_from_slice(&[2, 1, 1, 0]);
    e.extend_from_slice(&[0u8; 8]);
    e.extend_from_slice(&2u16.to_le_bytes()); // ET_EXEC
    e.extend_from_slice(&243u16.to_le_bytes()); // EM_RISCV
    e.extend_from_slice(&1u32.to_le_bytes());
    e.extend_from_slice(&TEXT.to_le_bytes());
    e.extend_from_slice(&ehsize.to_le_bytes());
    e.extend_from_slice(&0u64.to_le_bytes());
    e.extend_from_slice(&0u32.to_le_bytes());
    e.extend_from_slice(&64u16.to_le_bytes());
    e.extend_from_slice(&56u16.to_le_bytes());
    e.extend_from_slice(&1u16.to_le_bytes());
    e.extend_from_slice(&64u16.to_le_bytes());
    e.extend_from_slice(&0u16.to_le_bytes());
    e.extend_from_slice(&0u16.to_le_bytes());
    e.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
    e.extend_from_slice(&5u32.to_le_bytes()); // R|X
    e.extend_from_slice(&off.to_le_bytes());
    e.extend_from_slice(&TEXT.to_le_bytes());
    e.extend_from_slice(&TEXT.to_le_bytes());
    e.extend_from_slice(&(data.len() as u64).to_le_bytes());
    e.extend_from_slice(&(data.len() as u64).to_le_bytes());
    e.extend_from_slice(&8u64.to_le_bytes());
    e.extend_from_slice(&data);
    e
}

fn om(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_om"))
        .args(args)
        .output()
        .expect("spawn om")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// ABI flags matching the fib guest's layout (A=4, I=O=1).
const ABI: &[&str] = &[
    "--ram-log-words",
    "4",
    "--input-log-words",
    "1",
    "--output-log-words",
    "1",
    "--max-code-words",
    "256",
];

#[test]
fn keygen_prove_verify_roundtrip_and_run() {
    let dir: PathBuf = std::env::temp_dir().join(format!("om-cli-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let elf = dir.join("fib.elf");
    let vk = dir.join("vk.bin");
    let proof = dir.join("proof.bin");
    let inst = dir.join("inst.bin");
    std::fs::write(&elf, make_elf(&fib_program())).expect("write elf");
    let (elf, vk, proof, inst) = (
        elf.to_str().unwrap(),
        vk.to_str().unwrap(),
        proof.to_str().unwrap(),
        inst.to_str().unwrap(),
    );

    // keygen (test PCS profile for speed).
    let mut args = vec!["keygen", "--elf", elf, "--out", vk, "--profile", "test"];
    args.extend(ABI);
    let out = om(&args);
    assert!(out.status.success(), "keygen: {}", stdout(&out));
    assert!(stdout(&out).contains("vk_digest: "), "{}", stdout(&out));
    assert!(stdout(&out).contains("vk_bytes: "), "{}", stdout(&out));

    // prove.
    let out = om(&[
        "prove",
        "--vk",
        vk,
        "--elf",
        elf,
        "--out",
        proof,
        "--instance",
        inst,
    ]);
    assert!(out.status.success(), "prove: {}", stdout(&out));
    let s = stdout(&out);
    assert!(s.contains("T: 32"), "{s}");
    assert!(s.contains("exit_code: 0"), "{s}");
    assert!(s.contains("output_len: 8"), "{s}");
    assert!(s.contains("proof_bytes: "), "{s}");

    // verify accepts.
    let out = om(&["verify", "--vk", vk, "--instance", inst, "--proof", proof]);
    assert!(out.status.success(), "verify");
    assert_eq!(stdout(&out).trim(), "OK");

    // A flipped proof byte rejects with a nonzero exit.
    let mut bad = std::fs::read(proof).expect("read proof");
    let n = bad.len();
    bad[n - 1] ^= 1;
    std::fs::write(proof, &bad).expect("write bad proof");
    let out = om(&["verify", "--vk", vk, "--instance", inst, "--proof", proof]);
    assert!(!out.status.success(), "tampered proof must reject");
    assert!(!out.stderr.is_empty(), "rejection must explain on stderr");

    // run executes only and reports exit code 0 + output 13.
    let mut args = vec!["run", "--elf", elf];
    args.extend(ABI);
    let out = om(&args);
    assert!(out.status.success(), "run: {}", stdout(&out));
    let s = stdout(&out);
    assert!(s.contains("exit_code: 0"), "{s}");
    assert!(s.contains("output: 0d00000000000000"), "{s}");

    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn help_and_usage_errors() {
    for args in [
        vec!["--help"],
        vec!["keygen", "--help"],
        vec!["prove", "--help"],
        vec!["verify", "--help"],
        vec!["run", "--help"],
    ] {
        let out = om(&args);
        assert!(out.status.success(), "{args:?}");
        assert!(stdout(&out).contains("Usage"), "{args:?}");
    }
    // Unknown command / missing required option: nonzero, on stderr.
    let out = om(&["frobnicate"]);
    assert!(!out.status.success());
    let out = om(&["verify", "--vk", "x"]);
    assert!(!out.status.success());
    // Missing file: nonzero.
    let out = om(&["run", "--elf", "/nonexistent/om-test.elf"]);
    assert!(!out.status.success());
}
