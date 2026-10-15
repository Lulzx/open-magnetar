//! Verifier-side ports of `reference/tests/test_protocol.py`:
//! completeness (Ligerito `test` profile, transparent mock, real
//! `provable-120`), wrong-public-data / wrong-vk rejection, tampered
//! bytes and tampered in-memory proof fields, length rules,
//! round-trips through the verifier, and cheating provers.

mod common;

use std::collections::BTreeMap;
use std::sync::OnceLock;

use common::*;
use om_elf::Params;
use om_field::K;
use om_format::{
    PcsMode, PcsProfile, PcsProof, Proof, PublicInstance, VerifyingKey, decode_proof, encode_proof,
};
use om_prover::{Derived, keygen, prove_instance, prove_instance_with_trace_hook};
use om_transcript::Hasher;
use om_verifier::{
    ProofRef, verify, verify_bytes_strict_with_derived, verify_detailed_with_derived,
    verify_strict_with_derived, verify_with_derived,
};

/// Python `AP`: 16 RAM words, 2-word input/output regions.
fn ap() -> Params {
    Params {
        ram_log_words: 4,
        input_log_words: 1,
        output_log_words: 1,
        max_code_words: 256,
        hash_profile: Hasher::Sha256,
    }
}

const OUT_LEN_OFF: i64 = 112;
const OUT_VAL_OFF: i64 = 120;

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
        sd(5, 1, OUT_LEN_OFF),
        sd(3, 1, OUT_VAL_OFF),
        addi(10, 0, 0),
    ];
    p.extend(halt());
    p
}

/// Stores/loads of every width + register shifts (Python
/// `mem_shift_program`); exit 3.
fn mem_shift_program() -> Vec<u32> {
    let mut p = li32(2, 0x89AB_CDEF);
    p.extend([
        addi(1, 0, 1),
        slli(1, 1, 31),
        addi(3, 0, 5),
        sd(2, 1, 0),
        sb(3, 1, 1),
        sh(2, 1, 2),
        sw(2, 1, 4),
        ld(4, 1, 0),
        lb(5, 1, 1),
        lhu(6, 1, 2),
        lw(7, 1, 4),
        lbu(8, 1, 0),
        sll(9, 4, 3),
        srl(11, 4, 3),
        sraw(12, 2, 3),
        xor(13, 9, 11),
        xor(13, 13, 12),
        add(13, 13, 5),
        addi(14, 0, 8),
        sd(14, 1, OUT_LEN_OFF),
        sd(13, 1, OUT_VAL_OFF),
        addi(10, 0, 3),
    ]);
    p.extend(halt());
    p
}

fn make_vk_pcs(
    instrs: &[u32],
    pcs: PcsMode,
    profile: PcsProfile,
    t: u32,
) -> (VerifyingKey, BTreeMap<u64, u32>, u64) {
    let (code, entry) = program(instrs);
    let vk = keygen(
        code.clone(),
        entry,
        BTreeMap::new(),
        ap(),
        pcs,
        profile,
        2,
        t,
    )
    .expect("keygen");
    (vk, code, entry)
}

/// Python `make_vk`: Ligerito gets the `test` profile with `t = 8`.
fn make_vk(instrs: &[u32], pcs: PcsMode) -> (VerifyingKey, BTreeMap<u64, u32>, u64) {
    let (profile, t) = if pcs == PcsMode::Ligerito {
        (PcsProfile::Test, 8)
    } else {
        (PcsProfile::Provable120, 0)
    };
    make_vk_pcs(instrs, pcs, profile, t)
}

struct Fixture {
    vk: VerifyingKey,
    derived: Derived,
    code: BTreeMap<u64, u32>,
    entry: u64,
    inst: PublicInstance,
    proof: Proof,
    blob: Vec<u8>,
}

/// Python `Fixture` (fib, Ligerito `test` profile), proved once.
fn fixture() -> &'static Fixture {
    static FIX: OnceLock<Fixture> = OnceLock::new();
    FIX.get_or_init(|| {
        let (vk, code, entry) = make_vk(&fib_program(), PcsMode::Ligerito);
        let derived = Derived::new(&vk);
        let (inst, proof) = prove_instance(&vk, b"", None).expect("prove fib");
        let blob = encode_proof(&vk, &proof);
        Fixture {
            vk,
            derived,
            code,
            entry,
            inst,
            proof,
            blob,
        }
    })
}

// ------------------------------------------------------------ completeness

#[test]
fn fib_real_ligerito_accepts() {
    let f = fixture();
    assert_eq!(f.inst.t, 32);
    assert_eq!(
        u64::from_le_bytes(f.inst.output[..8].try_into().unwrap()),
        13
    );
    assert_eq!(f.inst.exit_code, 0);
    // Both forms, through the dispatching bool API and the strict one.
    assert!(verify(&f.vk, &f.inst, ProofRef::from(&f.proof)));
    assert!(verify(&f.vk, &f.inst, ProofRef::from(f.blob.as_slice())));
    assert!(verify_with_derived(&f.derived, &f.inst, (&f.proof).into()));
    assert!(verify_with_derived(&f.derived, &f.inst, (&f.blob).into()));
    assert!(verify_strict_with_derived(&f.derived, &f.inst, &f.proof).is_ok());
    assert!(verify_bytes_strict_with_derived(&f.derived, &f.inst, &f.blob).is_ok());
    // The reference layout assembles exactly 68 Mosaic claims.
    let v = verify_detailed_with_derived(&f.derived, &f.inst, &f.proof).expect("accepts");
    assert_eq!(v.mosaic_claims, 68);
    assert!(v.mosaic_claims <= om_mosaic::MAX_CLAIMS);
}

#[test]
fn blob_roundtrip_accepts() {
    let f = fixture();
    let di = f.derived.instance(f.inst.t).expect("instance");
    let shape = f.derived.proof_shape(&di);
    let again = decode_proof(&f.vk, &f.blob, f.inst.t, &shape).expect("decode");
    assert_eq!(encode_proof(&f.vk, &again), f.blob);
    assert!(verify(&f.vk, &f.inst, (&again).into()));
}

// ------------------------------------------------------------ wrong statement / vk

#[test]
fn wrong_public_data_rejects() {
    let f = fixture();
    let bads = [
        PublicInstance {
            output: 14u64.to_le_bytes().to_vec(),
            ..f.inst.clone()
        },
        PublicInstance {
            output: Vec::new(),
            ..f.inst.clone()
        },
        PublicInstance {
            exit_code: 1,
            ..f.inst.clone()
        },
        PublicInstance {
            t: 64,
            ..f.inst.clone()
        },
        PublicInstance {
            t: 16,
            ..f.inst.clone()
        },
        PublicInstance {
            input: b"x".to_vec(),
            ..f.inst.clone()
        },
    ];
    for bad in &bads {
        assert!(
            !verify_with_derived(&f.derived, bad, (&f.proof).into()),
            "{bad:?}"
        );
        assert!(!verify(&f.vk, bad, (&f.blob).into()), "{bad:?}");
        assert!(verify_strict_with_derived(&f.derived, bad, &f.proof).is_err());
    }
    // Non-power-of-two and out-of-range T (§11.3).
    for t in [0, 3, 48, 1 << 41] {
        let bad = PublicInstance {
            t,
            ..f.inst.clone()
        };
        assert!(!verify(&f.vk, &bad, (&f.proof).into()), "T={t}");
    }
}

#[test]
fn wrong_vk_rejects() {
    let f = fixture();
    let mut code = f.code.clone();
    // A different program (Python flips a bit of the third word).
    *code.get_mut(&(0x1000 + 4 * 2)).expect("third word") ^= 0x10_0000;
    let vk2 = keygen(
        code,
        f.entry,
        BTreeMap::new(),
        ap(),
        PcsMode::Ligerito,
        PcsProfile::Test,
        2,
        8,
    )
    .expect("keygen vk2");
    assert!(!verify(&vk2, &f.inst, (&f.blob).into()));
    assert!(!verify(&vk2, &f.inst, (&f.proof).into()));
}

// ------------------------------------------------------------ tampering

#[test]
fn tampered_blob_bytes_reject() {
    let f = fixture();
    let n = f.blob.len();
    let mut positions = vec![
        0,
        5,
        40,
        41,
        300,
        2000,
        4000,
        7000,
        9000,
        n - 3000,
        n - 700,
        n - 1,
    ];
    let mut rng = Rng(7);
    positions.extend((0..4).map(|_| rng.below(n as u64) as usize));
    for pos in positions.into_iter().filter(|&p| p < n) {
        let mut b = f.blob.clone();
        b[pos] ^= 0x01;
        assert!(!verify(&f.vk, &f.inst, b.as_slice().into()), "pos {pos}");
    }
}

#[test]
fn blob_length_rules() {
    let f = fixture();
    let mut longer = f.blob.clone();
    longer.push(0);
    assert!(!verify(&f.vk, &f.inst, longer.as_slice().into()));
    assert!(!verify(&f.vk, &f.inst, f.blob[..f.blob.len() - 1].into()));
    assert!(!verify(&f.vk, &f.inst, [].as_slice().into()));
    // Truncations at assorted points (spec §13.8: reject before use).
    for cut in [1, 6, 100, f.blob.len() / 2] {
        assert!(!verify(&f.vk, &f.inst, f.blob[..cut].into()), "cut {cut}");
    }
}

#[test]
fn tampered_proof_fields_reject() {
    let f = fixture();
    let reject = |p: &Proof, what: &str| {
        assert!(
            !verify_with_derived(&f.derived, &f.inst, p.into()),
            "tampered {what} accepted"
        );
    };
    let mut p = f.proof.clone();
    p.root[0] ^= 1;
    reject(&p, "root");
    let mut p = f.proof.clone();
    p.log_t += 1;
    reject(&p, "log_t");
    let mut p = f.proof.clone();
    p.spartan.v_w += K::ONE;
    reject(&p, "spartan v_w");
    let mut p = f.proof.clone();
    p.spartan.seg_vals[0] += K::ONE;
    reject(&p, "spartan seg_vals");
    let mut p = f.proof.clone();
    p.reg_bits[0] += K::ONE;
    reject(&p, "reg_bits");
    let mut p = f.proof.clone();
    p.reg.rw_evals[0] += K::ONE;
    reject(&p, "reg twist evals");
    let mut p = f.proof.clone();
    p.ram_bits[0] += K::ONE;
    reject(&p, "ram_bits");
    let mut p = f.proof.clone();
    p.ram_inc_wv += K::ONE;
    reject(&p, "ram_inc_wv");
    let mut p = f.proof.clone();
    p.ram.val_evals[0] += K::ONE;
    reject(&p, "ram twist evals");
    let mut p = f.proof.clone();
    p.shift.evals[0] += K::ONE;
    reject(&p, "shift router evals");
    let mut p = f.proof.clone();
    p.store.evals[0] += K::ONE;
    reject(&p, "store router evals");
    let mut p = f.proof.clone();
    p.shout.ra_evals[0] += K::ONE;
    reject(&p, "shout ra_evals");
    let mut p = f.proof.clone();
    p.mosaic.v_g += K::ONE;
    reject(&p, "mosaic v_g");
    let mut p = f.proof.clone();
    match &mut p.pcs_proof {
        PcsProof::Ligerito(rs, _) => rs.s[0] += K::ONE,
        PcsProof::Transparent(_) => unreachable!("ligerito fixture"),
    }
    reject(&p, "ring-switch s");
    let mut p = f.proof.clone();
    match &mut p.pcs_proof {
        PcsProof::Ligerito(_, lig) => lig.final_poly[0] += K::ONE,
        PcsProof::Transparent(_) => unreachable!("ligerito fixture"),
    }
    reject(&p, "ligerito final poly");
    // Shape tampers: shortened claim lists reject, never panic.
    let mut p = f.proof.clone();
    p.reg_bits.pop();
    reject(&p, "short reg_bits");
    let mut p = f.proof.clone();
    p.ram_bits.clear();
    reject(&p, "empty ram_bits");
    let mut p = f.proof.clone();
    p.root.clear();
    reject(&p, "empty root");
    let mut p = f.proof.clone();
    p.pcs_proof = PcsProof::Transparent(Vec::new());
    reject(&p, "pcs variant mismatch");
}

// ------------------------------------------------------------ transparent mock

#[test]
fn transparent_memory_and_shifts_accept() {
    let (vk, code, entry) = make_vk(&mem_shift_program(), PcsMode::Transparent);
    // Exit/T differential against the plain interpreter is proved in
    // om-prover; here the verifier must accept (Python asserts both).
    let _ = (code, entry);
    let (inst, proof) = prove_instance(&vk, b"", None).expect("prove");
    assert_eq!(inst.exit_code, 3);
    assert_eq!(inst.t, 64);
    assert!(verify(&vk, &inst, (&proof).into()));
    assert!(verify(
        &vk,
        &inst,
        encode_proof(&vk, &proof).as_slice().into()
    ));
    let bad_out = PublicInstance {
        output: vec![1u8; 8],
        ..inst.clone()
    };
    assert!(!verify(&vk, &bad_out, (&proof).into()));
    let bad_exit = PublicInstance {
        exit_code: 4,
        ..inst.clone()
    };
    assert!(!verify(&vk, &bad_exit, (&proof).into()));
    // Tampered transparent opening: one flipped G bit.
    let mut p = proof.clone();
    match &mut p.pcs_proof {
        PcsProof::Transparent(g) => g[0] = !g[0],
        PcsProof::Ligerito(..) => unreachable!("transparent vk"),
    }
    assert!(!verify(&vk, &inst, (&p).into()));
}

#[test]
fn transparent_input_is_bound() {
    // Copy the public input word to the output region (Python
    // `test_input_is_bound`).
    let mut prog = vec![
        addi(1, 0, 1),
        slli(1, 1, 31),
        ld(3, 1, 96),
        ld(4, 1, 104),
        sd(3, 1, OUT_LEN_OFF),
        sd(4, 1, OUT_VAL_OFF),
        addi(10, 0, 0),
    ];
    prog.extend(halt());
    let (vk, _, _) = make_vk(&prog, PcsMode::Transparent);
    let data = 0x1122_3344_5566_7788u64.to_le_bytes();
    let (inst, proof) = prove_instance(&vk, &data, None).expect("prove");
    assert_eq!(inst.output, data);
    assert!(verify(&vk, &inst, (&proof).into()));
    let mut reversed = data;
    reversed.reverse();
    let bad = PublicInstance {
        input: reversed.to_vec(),
        ..inst.clone()
    };
    assert!(!verify(&vk, &bad, (&proof).into()));
}

// ------------------------------------------------------------ cheating provers

fn prove_expect_reject(hook: &mut om_prover::TraceHook<'_>) {
    let (vk, _, _) = make_vk(&fib_program(), PcsMode::Transparent);
    // A cheating prover may fail while proving (a sub-prover's
    // claim-consistency assert, which Python's helper catches as an
    // exception and Rust surfaces as a panic); if it produces a
    // proof, the verifier must reject it.
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_instance_with_trace_hook(&vk, b"", hook)
    }));
    if let Ok(Ok((inst, proof))) = res {
        assert!(!verify(&vk, &inst, (&proof).into()));
    }
}

#[test]
fn cheating_ram_read_value_rejects() {
    prove_expect_reject(&mut |trace| {
        let j = trace
            .iter()
            .position(|r| r.rom.mem)
            .expect("a memory cycle");
        trace[j].ram_old ^= 0x10;
    });
}

#[test]
fn cheating_register_value_rejects() {
    prove_expect_reject(&mut |trace| {
        let j = trace
            .iter()
            .position(|r| r.rom.c_add && r.rd == 2)
            .expect("an add into x2");
        trace[j].v1 ^= 0x4;
    });
}

#[test]
fn cheating_shift_output_rejects() {
    prove_expect_reject(&mut |trace| {
        let j = trace
            .iter()
            .position(|r| r.shift_amt.is_some())
            .expect("a shift cycle");
        trace[j].dp.y ^= 0x2;
    });
}

#[test]
fn dishonest_output_claim_rejects() {
    let (vk, _, _) = make_vk(&fib_program(), PcsMode::Transparent);
    let (inst, proof) = prove_instance(&vk, b"", None).expect("prove");
    assert!(verify(&vk, &inst, (&proof).into()));
    let bad = PublicInstance {
        output: 5u64.to_le_bytes().to_vec(),
        ..inst.clone()
    };
    assert!(!verify(&vk, &bad, (&proof).into()));
}

// ------------------------------------------------------------ provable-120

struct P120 {
    vk: VerifyingKey,
    derived: Derived,
    inst: PublicInstance,
    proof: Proof,
    blob: Vec<u8>,
}

/// Python `TestProvable120EndToEnd.setUpClass`: default profile
/// (`provable-120`, `t = 177`, `gs = 2`), fib, proved once.
fn p120() -> &'static P120 {
    static FIX: OnceLock<P120> = OnceLock::new();
    FIX.get_or_init(|| {
        let (vk, _, _) = make_vk_pcs(
            &fib_program(),
            PcsMode::Ligerito,
            PcsProfile::Provable120,
            0,
        );
        let derived = Derived::new(&vk);
        let (inst, proof) = prove_instance(&vk, b"", None).expect("prove provable-120 fib");
        let blob = encode_proof(&vk, &proof);
        P120 {
            vk,
            derived,
            inst,
            proof,
            blob,
        }
    })
}

#[test]
fn provable120_profile_is_the_provable_one() {
    let f = p120();
    assert_eq!(f.vk.pcs_profile, PcsProfile::Provable120);
    // Python: ligerito_params(T.bit_length() - 1 + 11); for this
    // instance that is exactly its `ell` (5 + 11 = 16).
    let di = f.derived.instance(f.inst.t).expect("instance");
    assert_eq!(di.ell, (f.inst.t.trailing_zeros() as usize) + 11);
    let p = f.derived.ligerito_params(di.ell).expect("ligerito params");
    assert_eq!(p.ts, vec![177usize; p.levels()]);
    assert!(!p.gs.is_empty() && p.gs.iter().all(|&g| g == 2));
}

#[test]
fn provable120_accepts_and_mosaic_claims_exactly_68() {
    let f = p120();
    let v = verify_detailed_with_derived(&f.derived, &f.inst, &f.proof).expect("accepts");
    // §05.7 powers-of-gamma cap, and the exact §11.7/§13.2 count.
    assert!(v.mosaic_claims <= 256);
    assert_eq!(v.mosaic_claims, 68);
    assert!(verify_with_derived(
        &f.derived,
        &f.inst,
        f.blob.as_slice().into()
    ));
}

#[test]
fn provable120_tampered_blob_rejects() {
    let f = p120();
    let n = f.blob.len();
    for pos in [n - 1, n - 500, n / 2, 100] {
        let mut b = f.blob.clone();
        b[pos] ^= 1;
        assert!(!verify(&f.vk, &f.inst, b.as_slice().into()), "pos {pos}");
    }
}
