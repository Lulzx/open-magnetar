//! Deterministic fuzzing and differential testing suite (Spec 15 §15.6–15.7):
//! 1. Proof parser (`decode_proof`) and valid-proof byte/bit-flip rejection fuzzing (§15.7.1)
//! 2. Verifying-key (`decode_vk`), instance (`decode_instance`), and ELF loader (`om_elf::load`) fuzzing (§15.7.2)
//! 3. Whole-verifier (`verify`) fuzzing on mutated in-memory proofs (§15.7.3)
//! 4. Merkle multi-opening (`MerkleTree::verify`) adversarial fuzzing (§15.7.4)
//! 5. 4-way differential random RV64I program & invalid-access fuzzing across `Machine`,
//!    `VirtualMachine`, `om_circuit::circuit::check`, and `om_prover`/`om_verifier` (§15.6)

mod common;

use std::collections::BTreeMap;

use common::*;
use om_circuit::circuit as cpu;
use om_elf::Params;
use om_field::K;
use om_format::{
    PcsMode, PcsProfile, PcsProof, PublicInstance, decode_instance, decode_proof, decode_vk,
    encode_instance, encode_proof, encode_vk,
};
use om_isa::bytecode::{VirtualMachine, expand};
use om_isa::riscv::Machine;
use om_pcs::merkle::{MerkleTree, verify_multi};
use om_prover::{Derived, keygen, prove_instance};
use om_transcript::Hasher;
use om_verifier::verify;

/// Deterministic splitmix64 PRNG for reproducible fuzzing in CI.
struct FuzzRng(u64);

impl FuzzRng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn range(&mut self, n: usize) -> usize {
        (self.next_u64() as usize) % n
    }

    fn i64_range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next_u64() % ((hi - lo) as u64)) as i64
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next_u64() as u8).collect()
    }

    fn k(&mut self) -> K {
        let lo = self.next_u64() as u128;
        let hi = self.next_u64() as u128;
        K::from_u128(lo | (hi << 64))
    }
}

fn ap() -> Params {
    Params {
        ram_log_words: 4,
        input_log_words: 1,
        output_log_words: 1,
        max_code_words: 256,
        hash_profile: Hasher::Sha256,
    }
}

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

#[test]
fn fuzz_proof_parser_and_valid_proof_mutations() {
    let (code, entry) = program(&fib_program());
    let vk = keygen(
        code,
        entry,
        BTreeMap::new(),
        ap(),
        PcsMode::Ligerito,
        PcsProfile::Test,
        2,
        8,
    )
    .expect("keygen");
    let derived = Derived::new(&vk);
    let (inst, proof) = prove_instance(&vk, b"", None).expect("prove");
    let di = derived.instance(inst.t).expect("instance");
    let shape = derived.proof_shape(&di);
    let valid_blob = encode_proof(&vk, &proof);
    assert!(verify(&vk, &inst, valid_blob.as_slice().into()));

    let mut rng = FuzzRng(0xF022_0001);

    // 1. Arbitrary random blobs must never panic and must be rejected.
    for _ in 0..250 {
        let len = rng.range(4096);
        let garbage = rng.bytes(len);
        assert!(decode_proof(&vk, &garbage, inst.t, &shape).is_err());
        assert!(!verify(&vk, &inst, garbage.as_slice().into()));
    }

    // 2. Single-bit flips sampled densely across the entire valid proof blob must all be rejected.
    let stride = (valid_blob.len() / 200).max(1);
    for pos in (0..valid_blob.len()).step_by(stride) {
        let bit = 1u8 << (rng.range(8) as u32);
        let mut mutated = valid_blob.clone();
        mutated[pos] ^= bit;
        assert!(
            !verify(&vk, &inst, mutated.as_slice().into()),
            "mutated proof accepted at byte {pos} (bit {bit:#x})"
        );
    }

    // 3. Random multi-byte corruptions, truncations, and extensions of the valid proof.
    for _ in 0..100 {
        let mut mutated = valid_blob.clone();
        let n_flips = 1 + rng.range(4);
        for _ in 0..n_flips {
            let idx = rng.range(mutated.len());
            mutated[idx] ^= 1u8 << (rng.range(8) as u32);
        }
        assert!(!verify(&vk, &inst, mutated.as_slice().into()));
    }
    for trim in [1, 2, 7, 16, 32, 64, 128, valid_blob.len() / 2] {
        assert!(!verify(
            &vk,
            &inst,
            (&valid_blob[..valid_blob.len() - trim]).into()
        ));
    }
}

#[test]
fn fuzz_vk_instance_and_elf_parsers() {
    let (code, entry) = program(&fib_program());
    let vk = keygen(
        code,
        entry,
        BTreeMap::new(),
        ap(),
        PcsMode::Ligerito,
        PcsProfile::Provable120,
        2,
        0,
    )
    .expect("keygen");
    let valid_vk = encode_vk(&vk);
    let valid_inst = encode_instance(&PublicInstance {
        t: 32,
        input: b"abc".to_vec(),
        output: vec![1, 0, 0, 0, 0, 0, 0, 0],
        exit_code: 0,
    });

    let mut rng = FuzzRng(0xF022_0002);

    // Arbitrary random bytes into decode_vk, decode_instance, and om_elf::load.
    for _ in 0..300 {
        let len = rng.range(1024);
        let buf = rng.bytes(len);
        let _ = decode_vk(&buf);
        let _ = decode_instance(&buf);
        let _ = om_elf::load(&buf, &ap());
    }

    // Single-bit mutations of valid_vk must either fail decode_vk (e.g. digest mismatch)
    // or produce a different vk digest.
    for pos in 0..valid_vk.len() {
        let mut mutated = valid_vk.clone();
        mutated[pos] ^= 1;
        if let Ok(vk2) = decode_vk(&mutated) {
            assert_ne!(vk2.digest(), vk.digest());
        }
    }

    // Length-field overflow mutations in valid_inst must never allocate unboundedly or panic.
    for off in [13usize, 21] {
        if off + 8 <= valid_inst.len() {
            let mut mutated = valid_inst.clone();
            mutated[off..off + 8].copy_from_slice(&u64::MAX.to_le_bytes());
            assert!(decode_instance(&mutated).is_err());
        }
    }
}

#[test]
fn fuzz_in_memory_proof_mutations_rejected() {
    let (code, entry) = program(&fib_program());
    let vk = keygen(
        code,
        entry,
        BTreeMap::new(),
        ap(),
        PcsMode::Ligerito,
        PcsProfile::Test,
        2,
        8,
    )
    .expect("keygen");
    let (inst, proof) = prove_instance(&vk, b"", None).expect("prove");
    let mut rng = FuzzRng(0xF022_0003);

    for trial in 0..50 {
        let mut p = proof.clone();
        match trial % 5 {
            0 => {
                let idx = rng.range(p.reg_bits.len());
                p.reg_bits[idx] += rng.k();
            }
            1 => {
                let idx = rng.range(p.ram_bits.len());
                p.ram_bits[idx] += rng.k();
            }
            2 => {
                p.mosaic.v_g += K::ONE;
            }
            3 => {
                let idx = rng.range(p.spartan.seg_vals.len());
                p.spartan.seg_vals[idx] += K::ONE;
            }
            _ => {
                if let PcsProof::Ligerito(ref mut rs, ref mut lp) = p.pcs_proof {
                    if trial % 2 == 0 {
                        let idx = rng.range(rs.s.len());
                        rs.s[idx] += K::ONE;
                    } else {
                        let idx = rng.range(lp.final_poly.len());
                        lp.final_poly[idx] += K::ONE;
                    }
                }
            }
        }
        assert!(!verify(&vk, &inst, (&p).into()), "trial {trial} accepted");
    }
}

#[test]
fn fuzz_merkle_multi_opening_adversarial() {
    let mut rng = FuzzRng(0xF022_0004);
    let n_leaves = 64usize;
    let leaves: Vec<Vec<u8>> = (0..n_leaves).map(|_| rng.bytes(16)).collect();
    let tree = MerkleTree::new(Hasher::Sha256, &leaves);
    let root = tree.root();

    // Honest opening works.
    let valid_idx = vec![1usize, 5, 19, 42];
    let valid_auth = tree.open(&valid_idx).expect("valid open");
    let opened: Vec<Vec<u8>> = valid_idx.iter().map(|&i| leaves[i].clone()).collect();
    assert!(
        verify_multi(
            Hasher::Sha256,
            &root,
            n_leaves,
            &valid_idx,
            &opened,
            &valid_auth,
        )
        .is_ok()
    );

    // Unsorted or duplicate indices must be rejected.
    for bad_idx in [
        vec![5usize, 1, 19, 42],
        vec![1usize, 5, 5, 42],
        vec![1usize, 5, 19, 64],
        vec![],
    ] {
        let vals: Vec<Vec<u8>> = bad_idx
            .iter()
            .map(|&i| leaves[i % n_leaves].clone())
            .collect();
        assert!(
            verify_multi(
                Hasher::Sha256,
                &root,
                n_leaves,
                &bad_idx,
                &vals,
                &valid_auth,
            )
            .is_err()
        );
    }

    // Tampered auth path lengths and random bit flips in auth hashes must be rejected.
    assert!(
        verify_multi(
            Hasher::Sha256,
            &root,
            n_leaves,
            &valid_idx,
            &opened,
            &valid_auth[..valid_auth.len() - 1],
        )
        .is_err()
    );
    let mut extra_auth = valid_auth.clone();
    extra_auth.push(vec![0u8; 32]);
    assert!(
        verify_multi(
            Hasher::Sha256,
            &root,
            n_leaves,
            &valid_idx,
            &opened,
            &extra_auth,
        )
        .is_err()
    );
    for i in 0..valid_auth.len() {
        let mut bad_auth = valid_auth.clone();
        let b = rng.range(32);
        bad_auth[i][b] ^= 1;
        assert!(
            verify_multi(
                Hasher::Sha256,
                &root,
                n_leaves,
                &valid_idx,
                &opened,
                &bad_auth,
            )
            .is_err()
        );
    }
}

#[test]
fn fuzz_differential_4way_random_programs_and_invalid_accesses() {
    let mut rng = FuzzRng(0xF022_0005);
    let ram_log_words = 4u32;
    let cpu_par = cpu::Params {
        ram_log_words,
        log_cycles: 2,
    };

    // Part A: 30 random valid RV64I programs (including loads into x0, sub-word stores/loads,
    // shifts, branches, and ALU ops) checked across Machine, VirtualMachine, R1CS circuit,
    // and end-to-end proving/verification.
    for trial in 0..30 {
        let mut prog = prologue_ram_base(1);
        for reg in 2..=6 {
            prog.extend(li32(reg, rng.next_u64() as u32));
        }
        for _ in 0..16 {
            let r_dst = (rng.range(6) as u32) + 2; // x2..x7 (keep x1 = RAM_BASE)
            let r_a = (rng.range(6) as u32) + 2;
            let r_b = (rng.range(6) as u32) + 2;
            match rng.range(7) {
                0 => {
                    let op = match rng.range(10) {
                        0 => add(r_dst, r_a, r_b),
                        1 => sub(r_dst, r_a, r_b),
                        2 => xor(r_dst, r_a, r_b),
                        3 => or_(r_dst, r_a, r_b),
                        4 => and_(r_dst, r_a, r_b),
                        5 => slt(r_dst, r_a, r_b),
                        6 => sltu(r_dst, r_a, r_b),
                        7 => addw(r_dst, r_a, r_b),
                        8 => subw(r_dst, r_a, r_b),
                        _ => sll(r_dst, r_a, r_b),
                    };
                    prog.push(op);
                }
                1 => {
                    let imm = rng.i64_range(-2048, 2047);
                    let op = match rng.range(6) {
                        0 => addi(r_dst, r_a, imm),
                        1 => slti(r_dst, r_a, imm),
                        2 => sltiu(r_dst, r_a, imm),
                        3 => xori(r_dst, r_a, imm),
                        4 => ori(r_dst, r_a, imm),
                        _ => andi(r_dst, r_a, imm),
                    };
                    prog.push(op);
                }
                2 => {
                    let sh = rng.i64_range(0, 63);
                    let op = match rng.range(3) {
                        0 => slli(r_dst, r_a, sh),
                        1 => srli(r_dst, r_a, sh),
                        _ => srai(r_dst, r_a, sh),
                    };
                    prog.push(op);
                }
                3 => {
                    // Valid store into scratch words 0..11 (leaving I/O words 12..15 untouched).
                    let word_off = (rng.range(12) as i64) * 8;
                    let op = match rng.range(4) {
                        0 => sb(r_a, 1, word_off + rng.i64_range(0, 8)),
                        1 => sh(r_a, 1, word_off + 2 * rng.i64_range(0, 4)),
                        2 => sw(r_a, 1, word_off + 4 * rng.i64_range(0, 2)),
                        _ => sd(r_a, 1, word_off),
                    };
                    prog.push(op);
                }
                4 => {
                    // Valid load into r_dst OR x0 (testing x0 load semantics!).
                    let dst = if rng.range(3) == 0 { 0 } else { r_dst };
                    let word_off = (rng.range(12) as i64) * 8;
                    let op = match rng.range(7) {
                        0 => lb(dst, 1, word_off + rng.i64_range(0, 8)),
                        1 => lbu(dst, 1, word_off + rng.i64_range(0, 8)),
                        2 => lh(dst, 1, word_off + 2 * rng.i64_range(0, 4)),
                        3 => lhu(dst, 1, word_off + 2 * rng.i64_range(0, 4)),
                        4 => lw(dst, 1, word_off + 4 * rng.i64_range(0, 2)),
                        5 => lwu(dst, 1, word_off + 4 * rng.i64_range(0, 2)),
                        _ => ld(dst, 1, word_off),
                    };
                    prog.push(op);
                }
                5 => {
                    // ALU write to x0 (must remain 0).
                    prog.push(addi(0, r_a, rng.i64_range(-100, 100)));
                }
                _ => {
                    prog.push(fence());
                }
            }
        }
        prog.push(add(10, 2, 3));
        prog.extend(halt());

        let (code, entry) = program(&prog);
        let m = Machine::new(code.clone(), entry, &BTreeMap::new(), ram_log_words)
            .run(10000)
            .expect("Machine run");
        let expanded = expand(&code, entry);
        let vm = VirtualMachine::new(expanded.clone(), &BTreeMap::new(), ram_log_words)
            .run_padded(10000)
            .expect("VirtualMachine run");

        assert_eq!(m.exit_code, vm.exit_code, "trial {trial} exit_code");
        assert_eq!(m.regs[..32], vm.regs[..32], "trial {trial} regs");
        assert_eq!(m.ram, vm.ram, "trial {trial} ram");
        assert_eq!(m.instret, vm.instret, "trial {trial} instret");

        let w = cpu::witness(&vm.trace, &cpu_par, Some(vm.exit_code));
        let pub_in = cpu::public_inputs(&expanded, vm.exit_code);
        assert!(
            cpu::check(&w, &pub_in, &cpu_par, Some(&expanded)),
            "trial {trial} circuit check"
        );

        // Prove and verify every 6th trial through the full protocol.
        if trial % 6 == 0 {
            let vk = keygen(
                code,
                entry,
                BTreeMap::new(),
                ap(),
                PcsMode::Transparent,
                PcsProfile::Provable120,
                2,
                0,
            )
            .expect("keygen");
            let (inst, proof) = prove_instance(&vk, b"", None).expect("prove");
            assert_eq!(inst.exit_code, m.exit_code);
            assert!(verify(&vk, &inst, (&proof).into()));
        }
    }

    // Part B: Random out-of-range and misaligned memory accesses (including into x0)
    // must trap in BOTH Machine and VirtualMachine and be rejected by the prover.
    for trial in 0..20 {
        let dst = if trial % 2 == 0 { 0 } else { 2 }; // half into x0, half into x2
        let mut prog = prologue_ram_base(1);
        let bad_ins = match trial % 4 {
            0 => lw(dst, 1, 2),          // misaligned word load
            1 => ld(dst, 1, 4),          // misaligned doubleword load
            2 => lh(dst, 1, 1),          // misaligned halfword load
            _ => ld(dst, 1, 16 * 8 + 8), // out-of-range load beyond 2^A words
        };
        prog.push(bad_ins);
        prog.push(addi(10, 0, 7));
        prog.extend(halt());

        let (code, entry) = program(&prog);
        assert!(
            Machine::new(code.clone(), entry, &BTreeMap::new(), ram_log_words)
                .run(1000)
                .is_err(),
            "Machine must trap on invalid access (trial {trial})"
        );
        assert!(
            VirtualMachine::new(expand(&code, entry), &BTreeMap::new(), ram_log_words)
                .run(1000)
                .is_err(),
            "VirtualMachine must trap on invalid access (trial {trial})"
        );
        let vk = keygen(
            code,
            entry,
            BTreeMap::new(),
            ap(),
            PcsMode::Transparent,
            PcsProfile::Provable120,
            2,
            0,
        )
        .expect("keygen");
        assert!(
            prove_instance(&vk, b"", None).is_err(),
            "Prover must reject invalid access (trial {trial})"
        );
    }
}
