//! Port of `reference/tests/test_isa_cpu.py::TestCircuit` (spec 10):
//! segment layout, honest witnesses satisfying both relations on
//! programs covering ALU / loads / stores / shifts / branches / jumps /
//! HALT+padding, and rejection of corrupted witness bits per segment
//! class, wrong publics, ROM tampering, a non-halted trace end, and
//! JALR at every slot alignment.

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::*;
use om_circuit::circuit::{
    Cols, ST_EX, ST_HALT, ST_JF, ST_UPC, check, fl_pos, flag_pos, layout, num_w_cols,
    public_inputs, stats, violations, witness,
};
use om_circuit::{Params, PublicInputs};
use om_isa::bytecode::{Program, TraceRecord, VMResult, VirtualMachine, expand};

const A: u32 = 8;
const PAR: Params = Params {
    ram_log_words: A,
    log_cycles: 2,
};

fn with_halt(mut instrs: Vec<u32>) -> Vec<u32> {
    instrs.extend(halt());
    instrs
}

/// Python `make_trace`.
fn make_trace(instrs: &[u32]) -> (Program, VMResult) {
    let (code, entry) = program(instrs);
    let p = expand(&code, entry);
    let vm = VirtualMachine::new(p.clone(), &BTreeMap::new(), A)
        .run_padded(100_000)
        .expect("vm");
    (p, vm)
}

/// Python `TestCircuit.prog_mix`.
fn prog_mix() -> Vec<u32> {
    let mut v = prologue_ram_base(1);
    v.extend(li32(2, 0x89AB_CDEF));
    v.extend(li32(3, 5));
    v.extend([
        sd(2, 1, 0),
        lb(4, 1, 3),
        lhu(5, 1, 2),
        lw(6, 1, 0),
        sb(3, 1, 9),
        sh(2, 1, 10),
        sw(2, 1, 12),
        sll(7, 2, 3),
        srlw(8, 2, 3),
        sraw(9, 2, 3),
        srai(11, 2, 4),
        sub(12, 3, 2),
        slt(13, 2, 3),
        sltu(14, 3, 2),
        subw(15, 3, 2),
        xor(16, 2, 3),
        or_(17, 2, 3),
        and_(18, 2, 3),
        beq(3, 3, 8),
        addi(31, 0, 1),
        bltu(3, 2, 8),
        addi(31, 0, 2),
        auipc(19, 0),
        jalr(20, 19, 12),
        addi(31, 0, 3),
        addi(10, 6, 0),
    ]);
    with_halt(v)
}

fn honest() -> (Program, VMResult, Vec<Vec<bool>>, PublicInputs) {
    let (p, vm) = make_trace(&prog_mix());
    let w = witness(&vm.trace, &PAR, None);
    let pub_ = public_inputs(&p, vm.exit_code);
    (p, vm, w, pub_)
}

#[test]
fn layout_aligned_disjoint() {
    let segs = layout(&PAR);
    assert_eq!(segs.len(), 37);
    let mut spans: Vec<(usize, usize)> = segs
        .iter()
        .map(|s| (s.offset, s.offset + (1 << s.log_size)))
        .collect();
    spans.sort();
    for w in spans.windows(2) {
        assert!(w[0].1 <= w[1].0, "segments overlap: {w:?}");
    }
    for s in &segs {
        assert_eq!(s.offset % (1 << s.log_size), 0, "{}", s.name);
    }
    assert!(spans.last().unwrap().1 <= num_w_cols(&PAR));
    let owners: BTreeSet<&str> = segs.iter().map(|s| s.owner.as_str()).collect();
    for want in [
        "mosaic",
        "twist-reg",
        "twist-ram",
        "shout-bytecode",
        "router-shift",
    ] {
        assert!(owners.contains(want), "owner {want} missing");
    }
}

#[test]
fn honest_accepted() {
    let (p, _vm, w, pub_) = honest();
    assert_eq!(violations(&w, &pub_, &PAR, Some(&p)), Vec::<String>::new());
    assert!(check(&w, &pub_, &PAR, Some(&p)));
}

#[test]
fn other_programs_accepted() {
    let progs: Vec<Vec<u32>> = vec![
        with_halt(vec![addi(10, 0, 9)]),
        with_halt(vec![
            addi(5, 0, 0),
            addi(6, 0, 1),
            addi(7, 0, 6),
            add(28, 5, 6),
            addi(5, 6, 0),
            addi(6, 28, 0),
            addi(7, 7, -1),
            bne(7, 0, -16),
            addi(10, 5, 0),
        ]),
    ];
    for prog in &progs {
        let (p, vm) = make_trace(prog);
        let w = witness(&vm.trace, &PAR, None);
        assert!(check(&w, &public_inputs(&p, vm.exit_code), &PAR, Some(&p)));
    }
}

#[test]
fn rejects_wrong_public() {
    let (p, _vm, w, pub_) = honest();
    assert!(!check(
        &w,
        &PublicInputs {
            exit_code: pub_.exit_code ^ 1,
            ..pub_
        },
        &PAR,
        Some(&p)
    ));
    assert!(!check(
        &w,
        &PublicInputs {
            entry_upc: pub_.entry_upc + 1,
            ..pub_
        },
        &PAR,
        Some(&p)
    ));
}

fn find(trace: &[TraceRecord], pred: impl Fn(&TraceRecord) -> bool) -> usize {
    trace.iter().position(pred).expect("no such cycle")
}

#[test]
fn rejects_corruptions() {
    let (p, vm, w, pub_) = honest();
    let cc = Cols::new(&PAR);
    let n = PAR.cycles();
    let tr = &vm.trace;
    let cyc: BTreeMap<&str, usize> = BTreeMap::from([
        (
            "add",
            find(tr, |r| r.rom.c_add && !r.rom.sh_imm && r.rom.bsel == 0),
        ),
        ("load", find(tr, |r| r.rom.ln != 0 && r.rom.fill != 0)),
        ("store", find(tr, |r| r.rom.st_w != 0 && r.rom.st_w != 8)),
        ("shift", find(tr, |r| r.rom.q_lo != 0 && r.rom.bsel != 0)),
        ("branch", find(tr, |r| r.rom.br)),
        ("jalr", find(tr, |r| r.rom.jalr)),
        ("slt", find(tr, |r| r.rom.g_slt)),
        ("or", find(tr, |r| r.rom.g && r.rom.e)),
    ]);
    let fl = |name: &str| fl_pos(name).unwrap();
    // (field, bit, cycle key)
    let tests: Vec<(&str, usize, &str)> = vec![
        ("cin", 5, "add"),
        ("T0", 3, "add"),
        ("rdv", 0, "add"),
        ("v1", 10, "add"),
        ("Bop", 20, "add"),
        ("AND", 2, "or"),
        ("T2", 7, "or"),
        ("x3", 3, "load"),
        ("m", 1, "load"),
        ("L", 40, "load"),
        ("rw", 5, "load"),
        ("fl", fl("tb"), "load"),
        ("stc", 70, "store"),
        ("stc", 3, "store"),
        ("ridx", 0, "store"),
        ("off", 1, "store"),
        ("Gs", 4, "shift"),
        ("fl", fl("cond"), "shift"),
        ("shsrc", 9, "shift"),
        ("Y", 12, "shift"),
        ("fl", fl("take"), "branch"),
        ("nw", 40, "branch"),
        ("dynu", 3, "jalr"),
        ("fl", fl("rdslt"), "slt"),
        ("fl", fl("cout"), "slt"),
        ("upc", 1, "add"), // micro-PC chain
        ("Dw", 0, "add"),
    ];
    // State-segment corruptions (X1/X2/X3 and the S_in/S_out ties).
    for (name, bit) in [
        ("S_in", ST_UPC + 2),
        ("S_out", ST_UPC + 1),
        ("S_out", ST_HALT),
        ("S_in", ST_EX + 3),
        ("S_out", ST_JF),
    ] {
        for j in [0, w.len() - 1] {
            let mut w2 = w.clone();
            let col = cc.c(name, bit, 0);
            w2[j][col] = !w2[j][col];
            assert!(
                !violations(&w2, &pub_, &PAR, Some(&p)).is_empty(),
                "({name}, {bit}, {j}) not rejected"
            );
        }
    }
    let mut kinds = BTreeSet::new();
    for (field, bit, key) in tests {
        let k = cyc[key];
        let (j, t) = (k / n, k % n);
        let col = cc.c(field, bit, t);
        let mut w2 = w.clone();
        w2[j][col] = !w2[j][col];
        let v = violations(&w2, &pub_, &PAR, Some(&p));
        assert!(!v.is_empty(), "({field}, {bit}, {key}) not rejected");
        kinds.insert(field);
    }
    assert!(kinds.len() >= 10);
}

#[test]
fn rejects_rom_tamper_and_trap() {
    let (p, _vm, w, pub_) = honest();
    let cc = Cols::new(&PAR);
    // A decoded field that disagrees with ROM[upc].
    let mut w2 = w.clone();
    let col = cc.c("imm", 0, 0);
    w2[0][col] = !w2[0][col];
    assert!(!check(&w2, &pub_, &PAR, Some(&p)));
    // The trap flag set in the witness is rejected by the relation itself.
    let mut w3 = w.clone();
    let col = cc.c("rf", flag_pos("trap").unwrap(), 0);
    w3[0][col] = !w3[0][col];
    assert!(!violations(&w3, &pub_, &PAR, None).is_empty());
}

#[test]
fn not_halted_at_end_rejected() {
    let mut prog = vec![addi(5, 0, 1); 6];
    prog.push(addi(10, 0, 1));
    let (p, vm) = make_trace(&with_halt(prog));
    let tr = &vm.trace[..4];
    assert!(!tr.last().unwrap().rom.halted);
    let w = witness(tr, &PAR, None);
    assert!(!check(&w, &public_inputs(&p, vm.exit_code), &PAR, Some(&p)));
}

#[test]
fn jalr_at_every_slot_alignment() {
    for pad in 0..4 {
        let mut prog = vec![fence(); pad];
        prog.extend([auipc(5, 0), jalr(1, 5, 13), addi(10, 0, 7), addi(10, 0, 5)]);
        let (p, vm) = make_trace(&with_halt(prog));
        let w = witness(&vm.trace, &PAR, None);
        let pub_ = public_inputs(&p, vm.exit_code);
        assert_eq!(vm.exit_code, 5);
        assert!(check(&w, &pub_, &PAR, Some(&p)), "pad {pad}");
        // A prover that jumps to a different row for the dynamic target
        // is rejected.
        let k = find(&vm.trace, |r| r.rom.jalr);
        let cc = Cols::new(&PAR);
        let (j, t) = (k / PAR.cycles(), k % PAR.cycles());
        let mut w2 = w.clone();
        let col = cc.c("dynu", 2, t);
        w2[j][col] = !w2[j][col];
        assert!(!check(&w2, &pub_, &PAR, Some(&p)), "pad {pad}");
    }
}

#[test]
fn relations_agree_with_checker() {
    // The keygen conversion: rho = 10, nu = 14, and the om-spartan
    // SIMD checker (n_x = 0) accepts exactly what `check` accepts.
    let (_p, _vm, w, _pub) = honest();
    let (s1, s2) = om_circuit::relations(&PAR);
    assert_eq!((s1.rho, s1.nu), (10, 14));
    assert_eq!((s2.rho, s2.nu), (10, 14));
    let x: Vec<Vec<om_field::K>> = vec![Vec::new(); w.len()];
    assert!(om_spartan::simd_satisfied(&[s1, s2], &w, &x));
}

#[test]
fn stats_counts() {
    let s = stats(&PAR);
    assert_eq!(s.direct_bits_per_cycle, 1108);
    assert_eq!(s.nw, 8192);
}
