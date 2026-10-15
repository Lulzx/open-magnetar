//! Prover-side ports of `reference/tests/test_protocol.py` and
//! `test_params.py` assertions that belong to this crate: execution
//! differentials, keygen derivation/negatives, the §13.2 ledger and
//! the proof-size model. Accept/reject (verify) tests land in
//! `om-verifier`; here completeness evidence is execution agreement
//! plus the byte-for-byte vector in `vectors.rs`.

mod common;

use std::collections::BTreeMap;

use common::*;
use om_elf::Params;
use om_format::{FormatError, PcsMode, PcsProfile, VerifyingKey, choose_ad, encode_proof};
use om_isa::riscv::Machine;
use om_pcs::ligerito::{LigeritoParams, make_params, schedule};
use om_prover::params::{self, Machine as LedgerMachine};
use om_prover::{
    Derived, KeyError, ProverError, execute, keygen, prove, prove_instance,
    prove_instance_with_trace_hook,
};
use om_transcript::Hasher;

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

fn make_vk(instrs: &[u32], pcs: PcsMode) -> (VerifyingKey, BTreeMap<u64, u32>, u64) {
    let (code, entry) = program(instrs);
    let (profile, t) = if pcs == PcsMode::Ligerito {
        (PcsProfile::Test, 8)
    } else {
        (PcsProfile::Provable120, 0)
    };
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

// ------------------------------------------------------------ execution

#[test]
fn execute_fib_matches_isa_oracle() {
    let (vk, code, entry) = make_vk(&fib_program(), PcsMode::Ligerito);
    let ex = execute(&vk, b"", 1 << 20).expect("execute");
    // Python: T = 32, output 13, exit 0.
    assert_eq!(ex.instance.t, 32);
    assert_eq!(ex.trace.len(), 32);
    assert_eq!(ex.exit_code, 0);
    assert_eq!(
        u64::from_le_bytes(ex.instance.output[..8].try_into().unwrap()),
        13
    );
    // Differential: the plain RV64I interpreter agrees on the result.
    let mut m = Machine::new(code, entry, &BTreeMap::new(), 4);
    let res = m.run(10_000).expect("plain run");
    assert_eq!(ex.exit_code, res.exit_code);
    // Output word 15 holds the Fibonacci result (words 14/15 are the
    // output region for A=4, I=O=1).
    assert_eq!(res.ram.get(&15).copied().unwrap_or(0), 13);
    // The last cycle is HALTED and T is the least power of two > real.
    assert!(ex.trace.last().expect("trace").rom.halted);
}

#[test]
fn execute_mem_shift_matches_isa_oracle() {
    let (vk, code, entry) = make_vk(&mem_shift_program(), PcsMode::Transparent);
    let ex = execute(&vk, b"", 1 << 20).expect("execute");
    let mut m = Machine::new(code, entry, &BTreeMap::new(), 4);
    let res = m.run(10_000).expect("plain run");
    assert_eq!(ex.exit_code, res.exit_code);
    assert_eq!(ex.exit_code, 3);
    assert_eq!(ex.instance.t, 64);
    assert_eq!(ex.trace.len(), 64);
}

#[test]
fn execute_input_is_bound() {
    // Copy the public input word to the output region (Python
    // test_input_is_bound's program).
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
    let (inst, _proof) = prove_instance(&vk, &data, None).expect("prove");
    assert_eq!(inst.output, data);
}

#[test]
fn prove_transparent_fib_produces_proof() {
    // The transparent mock path end to end on the prover side
    // (acceptance is om-verifier's; here: it proves and encodes).
    let (vk, _, _) = make_vk(&fib_program(), PcsMode::Transparent);
    let (inst, proof) = prove_instance(&vk, b"", None).expect("prove transparent");
    assert_eq!(inst.t, 32);
    let blob = encode_proof(&vk, &proof);
    assert!(!blob.is_empty());
    // prove() returns the same proof.
    assert_eq!(prove(&vk, b"", None).expect("prove"), proof);
}

#[test]
fn private_input_rejected() {
    let (vk, _, _) = make_vk(&fib_program(), PcsMode::Transparent);
    assert_eq!(
        prove(&vk, b"", Some(b"secret")),
        Err(ProverError::PrivateInputNotSupported)
    );
}

#[test]
fn trace_hook_runs_and_skips_satisfiability_check() {
    // A cheating hook that corrupts one RAM read value: proving still
    // completes (Python's unchecked path). Rejection by the verifier
    // is om-verifier's test; the hook must actually have run.
    let (vk, _, _) = make_vk(&fib_program(), PcsMode::Transparent);
    let mut ran = false;
    let hook = &mut |trace: &mut Vec<om_isa::bytecode::TraceRecord>| {
        ran = true;
        let j = trace
            .iter()
            .position(|r| r.rom.mem)
            .expect("a memory cycle");
        trace[j].ram_old ^= 0x10;
    };
    let _ = prove_instance_with_trace_hook(&vk, b"", hook);
    assert!(ran);
}

// ------------------------------------------------------------ keygen

#[test]
fn keygen_derived_shape() {
    // Python TestKeygen.test_derived.
    let (vk, _, _) = make_vk(&fib_program(), PcsMode::Transparent);
    let d = Derived::new(&vk);
    assert_eq!((d.rho, d.nu), (10, 14));
    assert_eq!((d.ram_a, d.ram_d), (4, 1));
    assert_eq!(d.segments.len(), 37);
    let di = d.instance(32).expect("instance(32)");
    assert_eq!(
        di.ids["twist/ram/wa/1"], di.ids["twist/ram/ra0/1"],
        "RAM wa aliases ra0"
    );
    assert!(d.instance(3).is_err());
    assert!(d.instance(48).is_err());
}

#[test]
fn choose_ad_values() {
    // Python TestKeygen.test_choose_ad (choose_ad itself is om-format's).
    assert_eq!(choose_ad(6), (6, 2));
    assert_eq!(choose_ad(20), (20, 5));
    assert_eq!(choose_ad(24), (24, 6));
    assert_eq!(choose_ad(5), (8, 2));
    assert_eq!(choose_ad(4), (4, 1));
}

#[test]
fn keygen_negatives() {
    let (code, entry) = program(&fib_program());
    // entry_pc outside the code image.
    let bad_entry = keygen(
        code.clone(),
        0x2000,
        BTreeMap::new(),
        ap(),
        PcsMode::Ligerito,
        PcsProfile::Test,
        2,
        8,
    );
    assert_eq!(
        bad_entry,
        Err(KeyError::Format(FormatError::EntryPcNotInCode))
    );
    // test profile without queries.
    let bad_t = keygen(
        code.clone(),
        entry,
        BTreeMap::new(),
        ap(),
        PcsMode::Ligerito,
        PcsProfile::Test,
        2,
        0,
    );
    assert_eq!(
        bad_t,
        Err(KeyError::Format(FormatError::TestProfileNeedsQueries))
    );
    // program_digest mismatch: build a valid key, corrupt the stored
    // digest, and validate (Python VerifyingKey.__post_init__).
    let mut vk = keygen(
        code,
        entry,
        BTreeMap::new(),
        ap(),
        PcsMode::Ligerito,
        PcsProfile::Test,
        2,
        8,
    )
    .expect("valid vk");
    vk.program_digest[0] ^= 1;
    assert_eq!(vk.validate(), Err(FormatError::ProgramDigestMismatch));
}

// ------------------------------------------------------------ params ledger

const LOG_TS: [usize; 4] = [16, 20, 22, 24];

#[test]
fn ledger_provable_120_every_round() {
    for lt in LOG_TS {
        let l = params::ledger(lt, "provable-120", None, None);
        assert!(l.provable(), "log_t={lt}");
        for r in &l.rows {
            assert!(
                r.rbr_bits() >= 120.0 - 1e-9,
                "log_t={lt} step={} rbr={}",
                r.step,
                r.rbr_bits()
            );
        }
    }
}

#[test]
fn ledger_totals_close_to_120() {
    for lt in LOG_TS {
        let l = params::ledger(lt, "provable-120", None, None);
        let min_tot = l
            .rows
            .iter()
            .map(|r| r.tot_bits())
            .fold(f64::INFINITY, f64::min);
        assert!(min_tot > 119.9, "log_t={lt} min_tot={min_tot}");
        assert!(l.total_error_bits() > 114.0, "log_t={lt}");
    }
    // Spec §13.2's concrete numbers at T = 2^22.
    let l = params::ledger(22, "provable-120", None, None);
    assert!(
        (l.min_rbr_bits() - 120.0).abs() < 0.05,
        "{}",
        l.min_rbr_bits()
    );
    assert!(
        (l.total_error_bits() - 116.1).abs() < 0.05,
        "{}",
        l.total_error_bits()
    );
    let kib = params::proof_size_bytes(&l.params, true) / 1024.0;
    assert!((kib - 624.0).abs() < 1.0, "proof ~{kib} KiB");
    assert_eq!(l.machine.n_pack(), 26);
}

#[test]
fn ledger_conservative_bound_without_reps_fails() {
    for lt in [20, 22, 24] {
        let m = LedgerMachine::new(lt);
        let n = m.n_pack();
        let ks = schedule(n);
        let lv = ks.len();
        let p = LigeritoParams::new(n, ks, vec![2; lv], vec![177; lv]);
        let l = params::ledger(lt, "provable-120", None, Some(p));
        let min_gap = l
            .rows
            .iter()
            .filter(|r| r.step.contains("proximity gap"))
            .map(|r| r.rbr_bits())
            .fold(f64::INFINITY, f64::min);
        assert!(min_gap < 120.0, "log_t={lt}");
        assert!(l.min_rbr_bits() < 120.0, "log_t={lt}");
    }
}

#[test]
fn ledger_default_params_use_amplification() {
    for lt in LOG_TS {
        let l = params::ledger(lt, "provable-120", None, None);
        assert!(
            !l.params.gs.is_empty() && l.params.gs.iter().all(|&g| g >= 2),
            "log_t={lt}"
        );
        for r in l.rows.iter().filter(|r| r.step.contains("proximity gap")) {
            assert!(r.bits_direct.expect("gap bits") >= 120.0);
        }
    }
}

#[test]
fn ledger_conjectured_flagged() {
    for lt in LOG_TS {
        let l = params::ledger(lt, "conjectured-100", None, None);
        assert!(!l.provable(), "log_t={lt}");
        assert!(l.min_rbr_bits() < 120.0, "log_t={lt}");
        assert!(l.rows.iter().any(|r| !r.provable), "log_t={lt}");
    }
}

#[test]
fn ledger_formulas_match_sections() {
    let m = LedgerMachine::new(22);
    let l = params::ledger(22, "provable-120", None, None);
    let row = |name: &str| l.rows.iter().find(|r| r.step == name).expect("row");
    assert_eq!(
        row("Spartan inner sum-check (single, both relations)").tot_num,
        Some(28.0)
    );
    assert_eq!(row("Router shift").tot_num, Some((4 * (22 + 15)) as f64));
    assert_eq!(row("Router store").tot_num, Some((6 * (22 + 9)) as f64));
    assert_eq!(
        row("Ring switching").tot_num,
        Some((7 + 2 * m.n_pack()) as f64)
    );
    // §06 Lemma: eps_vsp = (8(rho+s) + 1 + 2 nu)/|K|.
    let sp: f64 = l
        .rows
        .iter()
        .filter(|r| r.step.starts_with("Spartan"))
        .map(|r| r.tot_num.expect("field row"))
        .sum();
    assert_eq!(sp, (8 * (10 + 20) + 1 + 28) as f64);
}

#[test]
fn ledger_mosaic_claim_cap() {
    let ok = params::ledger(
        22,
        "provable-120",
        Some(LedgerMachine {
            mosaic_claims: 256,
            ..LedgerMachine::new(22)
        }),
        None,
    );
    let bad = params::ledger(
        22,
        "provable-120",
        Some(LedgerMachine {
            mosaic_claims: 300,
            ..LedgerMachine::new(22)
        }),
        None,
    );
    assert!(ok.min_rbr_bits() >= 120.0 - 1e-9);
    assert!(bad.min_rbr_bits() < 120.0);
}

#[test]
fn proof_sizes_monotone() {
    let a = params::proof_size_bytes(&make_params(20, "provable-120", 2), true);
    let b = params::proof_size_bytes(&make_params(24, "provable-120", 2), true);
    assert!(a < b);
    assert!(params::proof_size_bytes(&make_params(24, "conjectured-100", 2), true) < b);
}

#[test]
fn report_summary_line() {
    let r = params::report(22, "provable-120");
    let last = r.lines().last().expect("summary line");
    assert_eq!(
        last,
        "min per-round bits 120.0; union of all totals: 116.1 bits; proof ~624 KiB"
    );
}
