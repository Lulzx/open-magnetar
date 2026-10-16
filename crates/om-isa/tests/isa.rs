//! ISA-level port of `reference/tests/test_isa_cpu.py`: the decoder,
//! interpreter, expansion and `VirtualMachine` vs `Machine` parts. The
//! circuit parts (`TestCircuit`) belong to spec 10 / om-circuit.

mod common;

use std::collections::BTreeMap;

use common::*;
use om_isa::bytecode::{COLUMNS, HALTED_UPC, TRAP_UPC, VirtualMachine, expand};
use om_isa::riscv::{ExecResult, Machine, Op, Trap, alu, decode};
use om_isa::{VMResult, kind, shift_apply, store_apply};

const A: u32 = 8;

type Both = (BTreeMap<u64, u32>, u64, ExecResult, VMResult);

fn run_both(instrs: &[u32], ram: &BTreeMap<usize, u64>) -> Both {
    let (code, entry) = program(instrs);
    let m = Machine::new(code.clone(), entry, ram, A)
        .run(100_000)
        .expect("machine");
    let mut vm = VirtualMachine::new(expand(&code, entry), ram, A);
    let vm = vm.run_padded(100_000).expect("vm");
    (code, entry, m, vm)
}

fn with_halt(mut instrs: Vec<u32>) -> Vec<u32> {
    instrs.extend(halt());
    instrs
}

// ---------------------------------------------------------------- decoder

#[test]
fn decoder_roundtrip_many() {
    // (word, name, rd, rs1, rs2, imm) with -1 meaning "don't check" for
    // register fields is avoided: check the fields Python checks.
    type DecCase = (u32, &'static str, Vec<(&'static str, i64)>);
    let name_cases: Vec<DecCase> = vec![
        (
            addi(5, 6, -1),
            "ADDI",
            vec![("rd", 5), ("rs1", 6), ("imm", -1)],
        ),
        (addi(5, 6, 2047), "ADDI", vec![("imm", 2047)]),
        (sub(1, 2, 3), "SUB", vec![("rd", 1), ("rs1", 2), ("rs2", 3)]),
        (
            sltu(31, 30, 29),
            "SLTU",
            vec![("rd", 31), ("rs1", 30), ("rs2", 29)],
        ),
        (srai(3, 4, 63), "SRAI", vec![("imm", 63)]),
        (srli(3, 4, 1), "SRLI", vec![("imm", 1)]),
        (slli(3, 4, 33), "SLLI", vec![("imm", 33)]),
        (sraiw(3, 4, 31), "SRAIW", vec![("imm", 31)]),
        (slliw(3, 4, 5), "SLLIW", vec![("imm", 5)]),
        (addiw(3, 4, -7), "ADDIW", vec![("imm", -7)]),
        (subw(3, 4, 5), "SUBW", vec![]),
        (sraw(3, 4, 5), "SRAW", vec![]),
        (lui(7, 0xFFFFF), "LUI", vec![("rd", 7), ("imm", -4096)]),
        (lui(7, 1), "LUI", vec![("imm", 4096)]),
        (auipc(7, 0x12345), "AUIPC", vec![("imm", 0x1234_5000)]),
        (jal(1, 2048), "JAL", vec![("rd", 1), ("imm", 2048)]),
        (jal(0, -4), "JAL", vec![("imm", -4)]),
        (jal(1, -(1 << 20)), "JAL", vec![("imm", -(1 << 20))]),
        (
            jalr(1, 2, -8),
            "JALR",
            vec![("rd", 1), ("rs1", 2), ("imm", -8)],
        ),
        (beq(1, 2, -4096), "BEQ", vec![("imm", -4096)]),
        (bne(1, 2, 4094), "BNE", vec![("imm", 4094)]),
        (blt(1, 2, 8), "BLT", vec![("imm", 8)]),
        (bge(1, 2, -2), "BGE", vec![("imm", -2)]),
        (bltu(1, 2, 100), "BLTU", vec![("imm", 100)]),
        (bgeu(1, 2, 2000), "BGEU", vec![("imm", 2000)]),
        (lb(1, 2, -1), "LB", vec![("imm", -1)]),
        (lhu(1, 2, 6), "LHU", vec![("imm", 6)]),
        (lwu(1, 2, 4), "LWU", vec![("imm", 4)]),
        (ld(1, 2, 2040), "LD", vec![("imm", 2040)]),
        (
            sb(1, 2, -1),
            "SB",
            vec![("rs1", 2), ("rs2", 1), ("imm", -1)],
        ),
        (sh(1, 2, 2), "SH", vec![("imm", 2)]),
        (sw(1, 2, -2048), "SW", vec![("imm", -2048)]),
        (sd(1, 2, 2047), "SD", vec![("imm", 2047)]),
        (fence(), "FENCE", vec![]),
        (ecall(), "ECALL", vec![]),
        (ebreak(), "EBREAK", vec![]),
    ];
    for (w, name, fields) in &name_cases {
        let ins = decode(*w);
        assert_eq!(ins.name(), *name, "{w:#x}");
        assert_eq!(ins.word, *w);
        for (k, v) in fields {
            let got = match *k {
                "rd" => i64::from(ins.rd),
                "rs1" => i64::from(ins.rs1),
                "rs2" => i64::from(ins.rs2),
                "imm" => ins.imm,
                _ => unreachable!(),
            };
            assert_eq!(got, *v, "{w:#x} {k}");
        }
    }
}

#[test]
fn decoder_illegal() {
    for w in [
        0x0000_0000u32,
        0xFFFF_FFFF,
        0x0200_0033,             // MUL (M ext)
        0x0000_100F,             // FENCE.I
        0x0000_1067,             // JALR f3!=0
        0x0000_4003 | (7 << 12), // load f3=7
        0x4000_1013,             // slli with bad funct6
        0x0020_0073,             // not ECALL/EBREAK
        // extra reserved-field cases beyond the Python list
        0x0000_0023 | (7 << 12),     // store f3=7
        0x0000_2063,                 // branch f3=2
        0x0400_103B,                 // OP-32 bad funct7/funct3
        i(0x20 << 5, 1, 1, 2, 0x1B), // SLLIW with f7=0x20 (bit25 path)
        0x3020_0073,                 // CSR-ish SYSTEM word
        0x0000_0063 | (2 << 12),     // branch f3=2 (dup shape)
    ] {
        assert_eq!(decode(w).op, Op::Illegal, "{w:#x}");
    }
    // SLLIW with instruction bit 25 set is reserved: f7 != 0.
    assert_eq!(decode(slliw(3, 4, 5) | (1 << 25)).op, Op::Illegal);
}

// helper so the table above can write a raw I-type word compactly
fn i(imm: u32, rs1: u32, f3: u32, rd: u32, opc: u32) -> u32 {
    ((imm & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opc
}

#[test]
fn decoder_random_regs() {
    let mut rng = Rng(1);
    for _ in 0..200 {
        let (rd, a, b) = (
            rng.below(32) as u32,
            rng.below(32) as u32,
            rng.below(32) as u32,
        );
        let ins = decode(xor(rd, a, b));
        assert_eq!(
            (
                ins.op,
                u32::from(ins.rd),
                u32::from(ins.rs1),
                u32::from(ins.rs2)
            ),
            (Op::Xor, rd, a, b)
        );
    }
}

// ------------------------------------------------------------ interpreter

#[test]
fn fibonacci() {
    let prog = with_halt(vec![
        addi(5, 0, 0),
        addi(6, 0, 1),
        addi(7, 0, 10),
        add(28, 5, 6),
        addi(5, 6, 0),
        addi(6, 28, 0),
        addi(7, 7, -1),
        bne(7, 0, -16),
        addi(10, 5, 0),
    ]);
    let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
    assert_eq!(m.exit_code, 55);
    assert_eq!(vm.exit_code, 55);
    assert_eq!(vm.instret, 3 + 10 * 5 + 3);
    let real = vm.trace.iter().filter(|r| !r.rom.halted).count();
    assert_eq!(real as u64, vm.instret);
    assert!(vm.trace.len().is_power_of_two());
    assert!(vm.trace.last().unwrap().rom.halted);
}

#[test]
fn alu_ops() {
    let mut prog = li32(5, 0x7FFF_FFFF);
    prog.extend(li32(6, (-5i32) as u32));
    prog.extend([
        addw(7, 5, 5),
        subw(8, 6, 5),
        slt(9, 6, 5),
        sltu(11, 6, 5),
        sltiu(12, 5, -1),
        slti(13, 6, -4),
        xori(14, 6, -1),
        ori(15, 5, 0x555),
        andi(16, 6, 0xFF),
        sub(17, 0, 5),
        add(18, 6, 6),
        addi(10, 0, 0),
    ]);
    let prog = with_halt(prog);
    let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
    assert_eq!(m.regs[7], 0xFFFF_FFFF_FFFF_FFFE);
    assert_eq!(m.regs[9], 1);
    assert_eq!(m.regs[11], 0);
    assert_eq!(m.regs[12], 1);
    assert_eq!(m.regs[13], 1);
    assert_eq!(m.regs[14], 4);
    assert_eq!(m.regs[16], 0xFB);
    assert_eq!(&m.regs[..], &vm.regs[..32]);
}

#[test]
fn shifts_all() {
    let vals: [u64; 6] = [
        0x8000_0000_0000_0001,
        0x0000_0000_F0F0_F0F1,
        0x1234_5678_9ABC_DEF0,
        0xFFFF_FFFF_8000_0000,
        1,
        0,
    ];
    type Enc = fn(u32, u32, u32) -> u32;
    let reg_ops: [(&str, Enc, Op); 6] = [
        ("sll", sll, Op::Sll),
        ("srl", srl, Op::Srl),
        ("sra", sra, Op::Sra),
        ("sllw", sllw, Op::Sllw),
        ("srlw", srlw, Op::Srlw),
        ("sraw", sraw, Op::Sraw),
    ];
    for (rr, enc, op) in reg_ops {
        for v in vals {
            for amt in [0u64, 1, 5, 17, 31, 32, 33, 63] {
                let mut prog = vec![addi(5, 0, 1), slli(5, 5, 63), addi(6, 0, amt as i64)];
                prog.extend(li64_x7(v));
                prog.extend([enc(10, 7, 6), add(10, 10, 0)]);
                let prog = with_halt(prog);
                let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
                let want = alu(op, v, amt);
                assert_eq!(m.exit_code, want, "{rr} {v:#x} {amt}");
                assert_eq!(vm.exit_code, want, "{rr} {v:#x} {amt}");
            }
        }
    }
    type EncI = fn(u32, u32, i64) -> u32;
    let imm_ops: [(&str, EncI, Op, i64); 6] = [
        ("slli", slli, Op::Slli, 63),
        ("srli", srli, Op::Srli, 63),
        ("srai", srai, Op::Srai, 63),
        ("slliw", slliw, Op::Slliw, 31),
        ("srliw", srliw, Op::Srliw, 31),
        ("sraiw", sraiw, Op::Sraiw, 31),
    ];
    for (ri, enc, op, mx) in imm_ops {
        for v in vals {
            for amt in [0i64, 1, 7, mx] {
                let mut prog = li64_x7(v);
                prog.push(enc(10, 7, amt));
                let prog = with_halt(prog);
                let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
                let want = alu(op, v, amt as u64);
                assert_eq!(m.exit_code, want, "{ri} {v:#x} {amt}");
                assert_eq!(vm.exit_code, want, "{ri} {v:#x} {amt}");
            }
        }
    }
}

#[test]
fn shift_expansion_cycle_counts_and_stages() {
    let prog = with_halt(vec![
        sll(3, 4, 5),
        sllw(3, 4, 5),
        slli(3, 4, 5),
        add(1, 2, 3),
    ]);
    let (code, entry) = program(&prog);
    let p = expand(&code, entry);
    let cyc: Vec<usize> = p.cycles_of_pc.values().copied().collect();
    assert_eq!(&cyc[..4], &[6, 5, 1, 1]);
    // stage wiring of the 64-bit register shift (spec 9.4)
    let head = p.upc_of_pc[&entry] as usize;
    for s in 0..6usize {
        let r = &p.rom[head + s];
        assert_eq!(r.head, s == 0);
        assert_eq!(r.rs1, if s == 0 { 4 } else { 32 });
        assert_eq!(r.rs2, 5);
        assert_eq!(r.rd, if s == 5 { 3 } else { 32 });
        assert_eq!(r.bsel, 1u8 << s);
        assert_eq!(r.q_lo, 1u64 << (1u32 << s));
        assert_eq!(r.q_hi, 1u8 << kind::SLL);
        assert!(r.b_imm && r.c_add && !r.w);
        assert_eq!(r.seq as usize, head + s + 1);
    }
    // word stages carry w=1
    let headw = head + 6;
    for s in 0..5usize {
        let r = &p.rom[headw + s];
        assert!(r.w);
        assert_eq!(r.q_hi, 1u8 << kind::SLLW);
    }
}

#[test]
fn loads_stores_all_widths() {
    let data: u64 = 0x8899_AABB_CCDD_EEFF;
    let mut prog = prologue_ram_base(1);
    prog.extend(store_const_x1(data));
    let mut n_ld = 0i64;
    type EncLd = fn(u32, u32, i64) -> u32;
    let loads: [(EncLd, i64); 7] = [
        (lb, 1),
        (lbu, 1),
        (lh, 2),
        (lhu, 2),
        (lw, 4),
        (lwu, 4),
        (ld, 8),
    ];
    for (enc, step) in loads {
        let mut off = 0;
        while off < 8 {
            prog.extend([enc(10, 1, off), sd(10, 1, 64 + 8 * n_ld)]);
            n_ld += 1;
            off += step;
        }
    }
    prog.push(addi(4, 0, -1));
    for off in 0..8 {
        prog.push(sb(4, 1, 512 + off));
    }
    prog.extend([sh(4, 1, 520 + 2), sw(4, 1, 528 + 4), sd(4, 1, 536)]);
    prog.extend([
        addi(5, 0, 0x7F),
        sb(5, 1, 520),
        sh(5, 1, 528),
        sw(5, 1, 544 + 4),
    ]);
    prog.push(addi(10, 0, 3));
    let prog = with_halt(prog);
    let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
    assert_eq!(m.ram, vm.ram);
    assert_eq!(&m.regs[..], &vm.regs[..32]);
    let w = |a: usize| m.ram.get(&(a >> 3)).copied().unwrap_or(0);
    assert_eq!(w(512), 0xFFFF_FFFF_FFFF_FFFF);
    assert_eq!(w(520), 0x0000_0000_FFFF_007F);
    assert_eq!(w(528), 0xFFFF_FFFF_0000_007F);
}

#[test]
fn signext_values() {
    let data: u64 = 0x8899_AABB_CCDD_EEFF;
    let mut base = prologue_ram_base(1);
    base.extend(store_const_x1(data));
    type EncLd = fn(u32, u32, i64) -> u32;
    let cases: [(EncLd, i64, u64); 10] = [
        (lb, 7, 0xFFFF_FFFF_FFFF_FF88),
        (lbu, 7, 0x88),
        (lh, 6, 0xFFFF_FFFF_FFFF_8899),
        (lhu, 6, 0x8899),
        (lw, 4, 0xFFFF_FFFF_8899_AABB),
        (lwu, 4, 0x8899_AABB),
        (lw, 0, 0xFFFF_FFFF_CCDD_EEFF),
        (lb, 1, 0xFFFF_FFFF_FFFF_FFEE),
        (ld, 0, data),
        (lh, 2, 0xFFFF_FFFF_FFFF_CCDD),
    ];
    for (enc, off, want) in cases {
        let mut p = base.clone();
        p.push(enc(10, 1, off));
        let p = with_halt(p);
        let (_, _, m, vm) = run_both(&p, &BTreeMap::new());
        assert_eq!(m.exit_code, want, "off {off}");
        assert_eq!(vm.exit_code, want, "off {off}");
    }
}

#[test]
fn branches() {
    type EncB = fn(u32, u32, i64) -> u32;
    let cases: [(EncB, i64, i64, u64); 12] = [
        (beq, 5, 5, 1),
        (beq, 5, 6, 0),
        (bne, 5, 6, 1),
        (bne, 5, 5, 0),
        (blt, -1, 1, 1),
        (blt, 1, -1, 0),
        (bge, -1, 1, 0),
        (bge, 3, 3, 1),
        (bltu, -1, 1, 0),
        (bltu, 1, -1, 1),
        (bgeu, -1, 1, 1),
        (bgeu, 2, 3, 0),
    ];
    for (enc, a, b, taken) in cases {
        let prog = with_halt(vec![
            addi(5, 0, a),
            addi(6, 0, b),
            enc(5, 6, 12),
            addi(10, 0, 0),
            jal(0, 8),
            addi(10, 0, 1),
        ]);
        let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
        assert_eq!(m.exit_code, taken, "{a} {b}");
        assert_eq!(vm.exit_code, taken, "{a} {b}");
    }
}

#[test]
fn jal_jalr_lui_auipc() {
    let prog = with_halt(vec![
        jal(1, 12),      // 0x1000: ra=0x1004, jump to 0x100c
        addi(10, 0, 99), // 0x1004
        jal(0, 16),      // 0x1008 -> 0x1018
        addi(5, 1, 0),   // 0x100c: x5 = ra
        jalr(6, 1, 0),   // 0x1010: x6 = 0x1014; jump to 0x1004
        addi(10, 0, 0),  // 0x1014 (unreached)
        auipc(7, 1),     // 0x1018: x7 = 0x1018 + 0x1000
        lui(8, 0x80000), // x8 = 0xFFFFFFFF80000000
        addi(9, 0, 0),
    ]);
    let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
    assert_eq!(m.regs[5], 0x1004);
    assert_eq!(m.regs[6], 0x1014);
    assert_eq!(m.regs[7], 0x2018);
    assert_eq!(m.regs[8], 0xFFFF_FFFF_8000_0000);
    assert_eq!(m.exit_code, 99);
    assert_eq!(&m.regs[..], &vm.regs[..32]);
    assert_eq!(vm.exit_code, 99);
}

#[test]
fn jalr_clears_low_bit() {
    let prog = with_halt(vec![
        auipc(5, 0),
        jalr(0, 5, 13), // target 0x100d -> 0x100c
        addi(10, 0, 7), // skipped
        addi(10, 0, 5), // 0x100c
    ]);
    let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
    assert_eq!(m.exit_code, 5);
    assert_eq!(vm.exit_code, 5);
    // the JALR trace record carries the dynamic target micro-PC
    let rec = vm.trace.iter().find(|r| r.rom.jalr).unwrap();
    assert_eq!(rec.next_upc, rec.dynu);
    assert_eq!(vm.trace[2].rom.rpc, 0x100c);
}

#[test]
fn traps() {
    let cases: Vec<Vec<u32>> = vec![
        vec![ebreak()],
        vec![addi(17, 0, 1), ecall()], // ECALL a7 != 0
        vec![lw(1, 0, 0)],             // out of range (addr 0)
        vec![addi(1, 0, 1), slli(1, 1, 31), lw(2, 1, 1)], // misaligned LW
        vec![addi(1, 0, 1), slli(1, 1, 31), lh(2, 1, 1)], // misaligned LH
        vec![addi(1, 0, 1), slli(1, 1, 31), sd(2, 1, 4)], // misaligned SD
        vec![addi(1, 0, 1), slli(1, 1, 31), ld(2, 1, 8 << A)], // past RAM end
        vec![0xFFFF_FFFF],             // illegal encoding
        vec![jal(0, 2)],               // misaligned jump target
        vec![jal(0, 4096)],            // jump out of code
        vec![auipc(5, 0), jalr(0, 5, 0x40)], // jalr to non-code
        vec![addi(5, 0, 1)],           // falls off the code end
    ];
    for (idx, ins) in cases.iter().enumerate() {
        let prog = with_halt(ins.clone());
        // for the fall-off case HALT follows in program order, so skip it
        let prog = if idx == cases.len() - 1 {
            ins.clone()
        } else {
            prog
        };
        let (code, entry) = program(&prog);
        let m = Machine::new(code.clone(), entry, &BTreeMap::new(), A).run(100);
        assert!(m.is_err(), "case {idx} machine: {m:?}");
        let mut vm = VirtualMachine::new(expand(&code, entry), &BTreeMap::new(), A);
        let v = vm.run(100);
        assert!(v.is_err(), "case {idx} vm: {v:?}");
    }
    // specific trap kinds
    let (code, entry) = program(&with_halt(vec![addi(17, 0, 1), ecall()]));
    assert_eq!(
        Machine::new(code, entry, &BTreeMap::new(), A)
            .run(100)
            .unwrap_err(),
        Trap::UnsupportedEcall
    );
    let (code, entry) = program(&with_halt(vec![ebreak()]));
    assert_eq!(
        Machine::new(code.clone(), entry, &BTreeMap::new(), A)
            .run(100)
            .unwrap_err(),
        Trap::Ebreak { pc: entry }
    );
    let mut vm = VirtualMachine::new(expand(&code, entry), &BTreeMap::new(), A);
    assert_eq!(vm.run(100).unwrap_err(), Trap::TrapRow);
}

#[test]
fn load_into_x0_preserves_access_checks_and_discards_value() {
    // Invalid/misaligned loads into x0 must trap in both Machine and VirtualMachine.
    for bad in [
        with_halt(vec![lw(0, 0, 1), addi(10, 0, 7)]),
        with_halt(vec![ld(0, 0, 0), addi(10, 0, 7)]),
        with_halt(
            prologue_ram_base(1)
                .into_iter()
                .chain([lw(0, 1, 2), addi(10, 0, 7)])
                .collect(),
        ),
        with_halt(
            prologue_ram_base(1)
                .into_iter()
                .chain([ld(0, 1, 4), addi(10, 0, 7)])
                .collect(),
        ),
    ] {
        let (code, entry) = program(&bad);
        assert!(
            Machine::new(code.clone(), entry, &BTreeMap::new(), A)
                .run(100)
                .is_err()
        );
        let mut vm = VirtualMachine::new(expand(&code, entry), &BTreeMap::new(), A);
        assert!(vm.run(100).is_err());
    }

    // Valid loads into x0 execute the memory read, enforce alignment/range, and leave x0 == 0.
    let mut valid = prologue_ram_base(1);
    valid.extend([
        addi(2, 0, 0x55),
        sd(2, 1, 0),
        ld(0, 1, 0),
        lw(0, 1, 4),
        lh(0, 1, 2),
        lb(0, 1, 1),
        addi(10, 0, 7),
    ]);
    let prog = with_halt(valid);
    let (code, entry, m, vm) = run_both(&prog, &BTreeMap::new());
    assert_eq!(m.exit_code, 7);
    assert_eq!(vm.exit_code, 7);
    assert_eq!(m.regs[0], 0);
    assert_eq!(vm.regs[0], 0);
    let p = expand(&code, entry);
    // Check that the ld x0, 0(x1) row has mem=true, alignment flags set, and ln=fill=0.
    let ld_pc = entry + 4 * 4;
    let row = p.rom[p.upc_of_pc[&ld_pc] as usize];
    assert_eq!(row.rd, 0);
    assert!(row.mem);
    assert!(row.a_h && row.a_w && row.a_d);
    assert_eq!(row.ln, 0);
    assert_eq!(row.fill, 0);
}

#[test]
fn x0_and_fence() {
    let prog = with_halt(vec![addi(0, 0, 5), fence(), add(0, 0, 0), addi(10, 0, 0)]);
    let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
    assert_eq!(m.regs[0], 0);
    assert_eq!(vm.regs[0], 0);
    for rec in &vm.trace {
        if rec.rd == 0 {
            assert_eq!(rec.rd_val, 0);
        }
    }
}

#[test]
fn max_cycles_trap() {
    let prog = vec![jal(0, 0)];
    let (code, entry) = program(&prog);
    assert_eq!(
        Machine::new(code.clone(), entry, &BTreeMap::new(), A)
            .run(10)
            .unwrap_err(),
        Trap::MaxCyclesExceeded
    );
    let mut vm = VirtualMachine::new(expand(&code, entry), &BTreeMap::new(), A);
    assert_eq!(vm.run(10).unwrap_err(), Trap::MaxCyclesExceeded);
}

// --------------------------------------------------------- VM vs Machine

#[test]
fn random_programs_vm_vs_machine() {
    let mut rng = Rng(42);
    let regs: Vec<u32> = (1..8).collect();
    type EncR = fn(u32, u32, u32) -> u32;
    let ops_rr: [EncR; 15] = [
        add, sub, xor, or_, and_, slt, sltu, sll, srl, sra, addw, subw, sllw, srlw, sraw,
    ];
    type EncI = fn(u32, u32, i64) -> u32;
    let ops_i: [EncI; 7] = [addi, slti, sltiu, xori, ori, andi, addiw];
    let ops_sh: [EncI; 3] = [slli, srli, srai];
    let stores: [(EncI, i64); 4] = [(sb, 1), (sh, 2), (sw, 4), (sd, 8)];
    let loads: [(EncI, i64); 7] = [
        (lb, 1),
        (lbu, 1),
        (lh, 2),
        (lhu, 2),
        (lw, 4),
        (lwu, 4),
        (ld, 8),
    ];
    for _trial in 0..25 {
        let mut prog = prologue_ram_base(1);
        for &r in &regs[1..] {
            prog.extend(li32(r, rng.next_u64() as u32));
        }
        for _ in 0..30 {
            match rng.below(6) {
                0 | 1 => prog.push(rng.choice(&ops_rr)(
                    *rng.choice(&regs[1..]),
                    *rng.choice(&regs[1..]),
                    *rng.choice(&regs[1..]),
                )),
                2 => prog.push(rng.choice(&ops_i)(
                    *rng.choice(&regs[1..]),
                    *rng.choice(&regs[1..]),
                    rng.below(4096) as i64 - 2048,
                )),
                3 => prog.push(rng.choice(&ops_sh)(
                    *rng.choice(&regs[1..]),
                    *rng.choice(&regs[1..]),
                    rng.below(64) as i64,
                )),
                4 => {
                    let (enc, w) = *rng.choice(&stores);
                    let off = w * rng.below((8 / w) as u64) as i64 + 8 * rng.below(4) as i64;
                    prog.push(enc(*rng.choice(&regs[1..]), 1, off));
                }
                _ => {
                    let (enc, w) = *rng.choice(&loads);
                    let off = w * rng.below((8 / w) as u64) as i64 + 8 * rng.below(4) as i64;
                    prog.push(enc(*rng.choice(&regs[1..]), 1, off));
                }
            }
        }
        prog.push(add(10, 2, 3));
        let prog = with_halt(prog);
        let (_, _, m, vm) = run_both(&prog, &BTreeMap::new());
        assert_eq!(m.exit_code, vm.exit_code);
        assert_eq!(&m.regs[..], &vm.regs[..32]);
        assert_eq!(m.ram, vm.ram);
        assert_eq!(m.instret, vm.instret);
        assert!(vm.trace.len().is_power_of_two());
    }
}

#[test]
fn trace_fields() {
    let prog = with_halt(vec![addi(5, 0, 3), sll(6, 5, 5), addi(10, 6, 0)]);
    let (_, _, _, vm) = run_both(&prog, &BTreeMap::new());
    let t = &vm.trace;
    assert_eq!(t[1].rd, 32); // first shift stage writes the temp register
    assert_eq!(t[1].shift_kind, Some(0));
    assert_eq!(t[1].shift_amt, Some(1));
    assert_eq!(vm.exit_code, 24);
    for rec in t {
        if rec.rd == 0 {
            assert_eq!(rec.rd_val, 0);
        }
        assert_eq!(rec.upc, rec.rom.upc);
        assert_eq!(rec.inc, rec.ram_old ^ rec.ram_new);
    }
}

// ------------------------------------------------------------- ROM shape

#[test]
fn rom_shape_and_wellformedness() {
    assert_eq!(COLUMNS.iter().map(|c| c.width).sum::<u32>(), 430);
    assert_eq!(COLUMNS.len(), 41);
    let prog = with_halt(vec![
        addi(5, 0, 3),
        sll(6, 5, 5),
        lw(7, 5, 0),
        sw(6, 5, 8),
        beq(5, 6, 8),
        lui(10, 0x12345),
    ]);
    let (code, entry) = program(&prog);
    let p = expand(&code, entry);
    assert!(p.rom[HALTED_UPC as usize].halted);
    assert_eq!(p.rom[HALTED_UPC as usize].rs1, 10);
    assert_eq!(p.rom[HALTED_UPC as usize].seq, HALTED_UPC);
    assert!(p.rom[TRAP_UPC as usize].trap);
    assert_eq!(p.rom[TRAP_UPC as usize].seq, TRAP_UPC);
    assert_eq!(p.entry_upc, 2);
    assert_eq!(p.entry_pc, entry);
    // rows in increasing pc, contiguous; head = first row of each instr
    let mut pcs: Vec<u64> = p.upc_of_pc.keys().copied().collect();
    pcs.sort_unstable();
    let mut expect = 2u32;
    for pc in pcs {
        assert_eq!(p.upc_of_pc[&pc], expect);
        expect += p.cycles_of_pc[&pc] as u32;
    }
    assert_eq!(p.rom.len() as u32, expect);
    for (idx, r) in p.rom.iter().enumerate() {
        assert_eq!(r.upc as usize, idx);
        assert_eq!(r.values().len(), 41);
        for c in COLUMNS {
            assert!(r.get(c.name).is_some(), "{}", c.name);
        }
        // spec 9.3 invariant: rd=0 rows have all result gates zero
        if r.rd == 0 {
            assert!(
                !r.c_add && !r.e && !r.g && !r.g_slt && !r.sh_imm,
                "row {idx}"
            );
            assert_eq!(r.bsel, 0);
            assert_eq!(r.ln, 0);
            assert_eq!(r.fill, 0);
            assert_eq!(r.kc, 0);
            assert_eq!(r.q_lo, 0);
            assert_eq!(r.q_hi, 0);
        }
        if !r.mem {
            assert_eq!(r.ln, 0);
            assert_eq!(r.fill, 0);
            assert_eq!(r.st_w, 0);
            assert!(!r.a_h && !r.a_w && !r.a_d, "row {idx}");
        } else {
            assert!(r.b_imm && !r.sub, "row {idx}");
        }
    }
    // last instruction falls off the end -> TRAP seq (here: ECALL's seq
    // is HALTED, so check a program without HALT)
    let (code2, entry2) = program(&[addi(5, 0, 1)]);
    let p2 = expand(&code2, entry2);
    assert_eq!(p2.rom[2].seq, TRAP_UPC);
    // branch to a missing pc -> tgt = TRAP
    let (code3, entry3) = program(&with_halt(vec![beq(0, 0, 4096)]));
    let p3 = expand(&code3, entry3);
    assert_eq!(p3.rom[2].tgt, TRAP_UPC);
}

#[test]
fn shift_and_store_apply_semantics() {
    assert_eq!(shift_apply(kind::SLL, 3, 5), 40);
    assert_eq!(
        shift_apply(kind::SRL, 2, 0xFFFF_FFFF_FFFF_FFFF),
        0x3FFF_FFFF_FFFF_FFFF
    );
    assert_eq!(
        shift_apply(kind::SRA, 2, 0xFFFF_FFFF_FFFF_FFFF),
        0xFFFF_FFFF_FFFF_FFFF
    );
    assert_eq!(shift_apply(kind::SLLW, 31, 1), 0xFFFF_FFFF_8000_0000);
    assert_eq!(
        shift_apply(kind::SRLW, 0, 0xFFFF_FFFF_8000_0000),
        0xFFFF_FFFF_8000_0000
    );
    assert_eq!(
        shift_apply(kind::SRAW, 31, 0x8000_0000),
        0xFFFF_FFFF_FFFF_FFFF
    );
    assert_eq!(
        shift_apply(kind::SEXT32, 0, 0x8000_0000),
        0xFFFF_FFFF_8000_0000
    );
    assert_eq!(
        shift_apply(kind::ZEXT32, 0, 0xFFFF_FFFF_8000_0000),
        0x8000_0000
    );
    // invalid amounts -> 0 (C7)
    assert_eq!(shift_apply(kind::SLLW, 32, 1), 0);
    assert_eq!(shift_apply(kind::SEXT32, 1, 1), 0);
    assert_eq!(shift_apply(kind::ZEXT32, 5, 1), 0);
    // store routing
    assert_eq!(store_apply(0, 2, 0, 0xAB), 0xAB_0000);
    assert_eq!(
        store_apply(1, 2, 0xFFFF_FFFF_FFFF_FFFF, 0),
        0xFFFF_FFFF_0000_FFFF
    );
    assert_eq!(store_apply(3, 0, 0xFFFF_FFFF_FFFF_FFFF, 7), 7);
}

#[test]
fn ram_initial_words_visible_to_both() {
    let mut ram = BTreeMap::new();
    ram.insert(0usize, 0xDEAD_BEEFu64);
    ram.insert(3usize, 0u64); // zero words are dropped, as in Python
    let mut prog = prologue_ram_base(1);
    prog.extend([lw(10, 1, 0), ld(11, 1, 24)]);
    let prog = with_halt(prog);
    let (_, _, m, vm) = run_both(&prog, &ram);
    assert_eq!(m.exit_code, 0xFFFF_FFFF_DEAD_BEEF);
    assert_eq!(vm.exit_code, m.exit_code);
    assert_eq!(m.regs[11], 0);
    assert!(!m.ram.contains_key(&3));
}
