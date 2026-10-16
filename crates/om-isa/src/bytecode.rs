//! Virtual instruction set, RV64I -> bytecode-table expansion, and the
//! virtual machine. Mirrors `reference/openmagnetar/bytecode.py`; see
//! `docs/spec/09-isa.md`. A *virtual instruction* is one ROM [`Row`]; the
//! circuit (spec 10) is a fixed datapath steered by the row's columns.
//! [`datapath`] is the single source of truth for per-cycle intermediates.

use std::collections::BTreeMap;

use crate::riscv::{Instr, M32, M64, Op, RAM_BASE, Trap, decode, sext};

pub const HALTED_UPC: u32 = 0;
pub const TRAP_UPC: u32 = 1;
/// Virtual register used by multi-cycle expansions.
pub const TEMP_REG: u8 = 32;

/// Shift kinds of CONVENTIONS C7 (Python `KIND` values).
pub mod kind {
    pub const SLL: u8 = 0;
    pub const SRL: u8 = 1;
    pub const SRA: u8 = 2;
    pub const SLLW: u8 = 3;
    pub const SRLW: u8 = 4;
    pub const SRAW: u8 = 5;
    pub const SEXT32: u8 = 6;
    pub const ZEXT32: u8 = 7;
}

/// Python `KIND[name]`.
pub fn kind_of(name: &str) -> Option<u8> {
    Some(match name {
        "SLL" => kind::SLL,
        "SRL" => kind::SRL,
        "SRA" => kind::SRA,
        "SLLW" => kind::SLLW,
        "SRLW" => kind::SRLW,
        "SRAW" => kind::SRAW,
        "SEXT32" => kind::SEXT32,
        "ZEXT32" => kind::ZEXT32,
        _ => return None,
    })
}

/// One ROM column descriptor (Python `Column`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Column {
    pub name: &'static str,
    pub width: u32,
    pub meaning: &'static str,
}

const fn col(name: &'static str, width: u32, meaning: &'static str) -> Column {
    Column {
        name,
        width,
        meaning,
    }
}

/// The 26 one-bit flags, in `FLAG_NAMES` order.
pub const FLAG_NAMES: [&str; 26] = [
    "head", "halted", "ecall", "trap", "b_imm", "sub", "w", "c_add", "e", "g", "f_ltu", "f_lts",
    "f_cmp", "g_slt", "f_eq", "br", "inv", "sh_imm", "mem", "a_h", "a_w", "a_d", "jalr", "ldsb",
    "ldsh", "ldsw",
];

/// The ROM columns in `bytecode.COLUMNS` order (430 bits total). This is
/// also the order in which spec 07 concatenates a read value's columns.
pub const COLUMNS: [Column; 41] = [
    col("upc", 32, "micro-PC of this row (identity column)"),
    col("rpc", 64, "RV64I pc of the instruction this row belongs to"),
    col(
        "rs1",
        6,
        "register read port 1 (6-bit index; virtual regs 32..63)",
    ),
    col("rs2", 6, "register read port 2"),
    col("rd", 6, "register write port (0 = no write)"),
    col(
        "imm",
        64,
        "sign-extended immediate (ALU B operand / address offset)",
    ),
    col(
        "kc",
        64,
        "constant result word (LUI, AUIPC, link address pc+4)",
    ),
    col("seq", 32, "next micro-PC when not taken / not indirect"),
    col("tgt", 32, "next micro-PC when a branch is taken"),
    col(
        "head",
        1,
        "first row of an RV64I instruction (valid JALR/branch target)",
    ),
    col("halted", 1, "HALTED padding row (binds exit code)"),
    col("ecall", 1, "HALT row: requires a7 (rs2 value) = 0"),
    col("trap", 1, "unprovable row: circuit requires trap = 0"),
    col("b_imm", 1, "ALU B operand is imm (else rs2 value)"),
    col("sub", 1, "adder subtracts (B inverted, carry-in 1)"),
    col(
        "w",
        1,
        "sign-extend adder result from bit 31 (ADDW, SUBW, ADDIW, word shift stages)",
    ),
    col("c_add", 1, "result gets adder output S'"),
    col("e", 1, "result gets XOR of operands (XOR, OR)"),
    col("g", 1, "result gets AND of operands (AND, OR)"),
    col("f_ltu", 1, "unsigned compare (SLTU, BLTU, BGEU)"),
    col("f_lts", 1, "signed compare (SLT, BLT, BGE)"),
    col("f_cmp", 1, "f_ltu or f_lts"),
    col(
        "g_slt",
        1,
        "write comparison bit to rd (SLT, SLTU, SLTI, SLTIU)",
    ),
    col("f_eq", 1, "equality test (BEQ, BNE)"),
    col("br", 1, "conditional branch"),
    col("inv", 1, "invert branch condition"),
    col("sh_imm", 1, "static (unconditional) shift"),
    col("mem", 1, "RAM access (load or store)"),
    col("a_h", 1, "access width >= 2 bytes (alignment)"),
    col("a_w", 1, "access width >= 4 bytes"),
    col("a_d", 1, "access width = 8 bytes"),
    col("jalr", 1, "indirect jump: next micro-PC is dynamic"),
    col("ldsb", 1, "signed byte load (sign = extracted bit 7)"),
    col("ldsh", 1, "signed halfword load (bit 15)"),
    col("ldsw", 1, "signed word load (bit 31)"),
    col(
        "bsel",
        6,
        "one-hot: bit of rs2 value that conditions a shift stage (0 = unconditional)",
    ),
    col("ln", 8, "load: byte lanes copied from the extracted word"),
    col("fill", 8, "load: byte lanes filled with the sign bit"),
    col("st_w", 4, "store width one-hot {SB,SH,SW,SD} (router Q_st)"),
    col(
        "Q_lo",
        64,
        "one-hot shift amount (router Q_lo); 0 if no shift",
    ),
    col("Q_hi", 8, "one-hot shift kind (router Q_hi); 0 if no shift"),
];

/// Python `COLUMN_BY_NAME[name]`.
pub fn column_by_name(name: &str) -> Option<&'static Column> {
    COLUMNS.iter().find(|c| c.name == name)
}

/// One bytecode ROM row: a virtual instruction (Python row dict). Vector
/// columns hold bit `i` at bit `i` of the integer, as in Python.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Row {
    pub upc: u32,
    pub rpc: u64,
    pub rs1: u8,
    pub rs2: u8,
    pub rd: u8,
    pub imm: u64,
    pub kc: u64,
    pub seq: u32,
    pub tgt: u32,
    pub head: bool,
    pub halted: bool,
    pub ecall: bool,
    pub trap: bool,
    pub b_imm: bool,
    pub sub: bool,
    pub w: bool,
    pub c_add: bool,
    pub e: bool,
    pub g: bool,
    pub f_ltu: bool,
    pub f_lts: bool,
    pub f_cmp: bool,
    pub g_slt: bool,
    pub f_eq: bool,
    pub br: bool,
    pub inv: bool,
    pub sh_imm: bool,
    pub mem: bool,
    pub a_h: bool,
    pub a_w: bool,
    pub a_d: bool,
    pub jalr: bool,
    pub ldsb: bool,
    pub ldsh: bool,
    pub ldsw: bool,
    /// 6-bit one-hot (or zero): which bit of `rs2` conditions a shift stage.
    pub bsel: u8,
    /// Load: byte lanes copied from the extracted word.
    pub ln: u8,
    /// Load: byte lanes filled with the sign.
    pub fill: u8,
    /// Store width one-hot `{SB, SH, SW, SD}`; zero on non-stores.
    pub st_w: u8,
    /// One-hot shift amount 0..63; zero if no shift.
    pub q_lo: u64,
    /// One-hot shift kind 0..7; zero if no shift.
    pub q_hi: u8,
}

impl Row {
    /// The flag named `name` (one of [`FLAG_NAMES`]), if it exists.
    pub fn flag(&self, name: &str) -> Option<bool> {
        Some(match name {
            "head" => self.head,
            "halted" => self.halted,
            "ecall" => self.ecall,
            "trap" => self.trap,
            "b_imm" => self.b_imm,
            "sub" => self.sub,
            "w" => self.w,
            "c_add" => self.c_add,
            "e" => self.e,
            "g" => self.g,
            "f_ltu" => self.f_ltu,
            "f_lts" => self.f_lts,
            "f_cmp" => self.f_cmp,
            "g_slt" => self.g_slt,
            "f_eq" => self.f_eq,
            "br" => self.br,
            "inv" => self.inv,
            "sh_imm" => self.sh_imm,
            "mem" => self.mem,
            "a_h" => self.a_h,
            "a_w" => self.a_w,
            "a_d" => self.a_d,
            "jalr" => self.jalr,
            "ldsb" => self.ldsb,
            "ldsh" => self.ldsh,
            "ldsw" => self.ldsw,
            _ => return None,
        })
    }

    /// The column named `name` as an integer (Python `row[name]`), for
    /// Shout table construction by column name. `None` for unknown names.
    pub fn get(&self, name: &str) -> Option<u64> {
        Some(match name {
            "upc" => u64::from(self.upc),
            "rpc" => self.rpc,
            "rs1" => u64::from(self.rs1),
            "rs2" => u64::from(self.rs2),
            "rd" => u64::from(self.rd),
            "imm" => self.imm,
            "kc" => self.kc,
            "seq" => u64::from(self.seq),
            "tgt" => u64::from(self.tgt),
            "bsel" => u64::from(self.bsel),
            "ln" => u64::from(self.ln),
            "fill" => u64::from(self.fill),
            "st_w" => u64::from(self.st_w),
            "Q_lo" => self.q_lo,
            "Q_hi" => u64::from(self.q_hi),
            other => u64::from(self.flag(other)?),
        })
    }

    /// All 41 column values in [`COLUMNS`] order.
    pub fn values(&self) -> [u64; 41] {
        let mut out = [0u64; 41];
        for (i, c) in COLUMNS.iter().enumerate() {
            out[i] = self.get(c.name).expect("COLUMNS name");
        }
        out
    }
}

/// Python `blank_row()`: an all-zero row.
pub fn blank_row() -> Row {
    Row::default()
}

// ---------------------------------------------------------------------------
// Router semantics (C7)
// ---------------------------------------------------------------------------

/// The shift routing semantics of C7 (Python `shift_apply`). Invalid
/// amounts map every output to zero.
///
/// # Panics
/// On `kind > 7`, matching Python's `ValueError`.
pub fn shift_apply(kind: u8, amt: u32, src: u64) -> u64 {
    let lo = src & M32;
    match kind {
        kind::SLL => {
            if amt >= 64 {
                0
            } else {
                src << amt
            }
        }
        kind::SRL => {
            if amt >= 64 {
                0
            } else {
                src >> amt
            }
        }
        kind::SRA => {
            if amt >= 64 {
                if src >> 63 == 1 { M64 } else { 0 }
            } else {
                (src as i64 >> amt) as u64
            }
        }
        kind::SLLW => {
            if amt < 32 {
                sext((src << amt) & M32, 32) as u64
            } else {
                0
            }
        }
        kind::SRLW => {
            if amt < 32 {
                sext(lo >> amt, 32) as u64
            } else {
                0
            }
        }
        kind::SRAW => {
            if amt < 32 {
                (sext(lo, 32) >> amt) as u64
            } else {
                0
            }
        }
        kind::SEXT32 => {
            if amt == 0 {
                sext(lo, 32) as u64
            } else {
                0
            }
        }
        kind::ZEXT32 => {
            if amt == 0 {
                lo
            } else {
                0
            }
        }
        _ => panic!("shift_apply: bad kind {kind}"),
    }
}

/// New RAM word of a store (Python `store_apply`). `width_sel` in 0..3
/// (SB, SH, SW, SD); `off` is the low 3 bits of the byte address.
pub fn store_apply(width_sel: u8, off: u32, old: u64, src: u64) -> u64 {
    assert!(width_sel <= 3, "store_apply: bad width_sel {width_sel}");
    let nb = 1u32 << width_sel;
    let field: u64 = if nb == 8 { M64 } else { (1u64 << (8 * nb)) - 1 };
    let mask = field << (8 * off);
    (old & !mask) | ((src << (8 * off)) & mask)
}

/// Index of the single set bit, or `None` for zero (Python
/// `onehot_index`).
///
/// # Panics
/// If `x` has more than one bit set, matching Python's `assert`.
pub fn onehot_index(x: u64) -> Option<u32> {
    if x == 0 {
        return None;
    }
    assert!(x & (x - 1) == 0, "not one-hot");
    Some(x.trailing_zeros())
}

/// Bit `i` of `x` as 0/1 (Python `bit`).
pub fn bit(x: u64, i: u32) -> u64 {
    (x >> i) & 1
}

/// Byte mask of a lane set (Python `lane_mask`).
pub fn lane_mask(lanes: u8) -> u64 {
    let mut m = 0u64;
    for k in 0..8 {
        if (lanes >> k) & 1 == 1 {
            m |= 0xFFu64 << (8 * k);
        }
    }
    m
}

// ---------------------------------------------------------------------------
// Per-cycle datapath (the semantics the circuit arithmetizes)
// ---------------------------------------------------------------------------

/// All per-cycle datapath intermediates (Python `datapath` dict). Field
/// names are the Python keys in snake_case: `Bop`→`bop`, `S`→`s`,
/// `Dw`→`dw`, `Sp`→`sp`, `X`→`x`, `AND`→`and_val`, `T0..T2`→`t0..t2`,
/// `Y`→`y`, `Gs`→`gs`, `L`→`l`. One-bit values are `bool`; `rdslt` and
/// `eqres` keep Python's integer 0/1 values as `u64` because `rdslt` is
/// XORed into `rdv`. Python's `shift` entry is `(kind, amt)` when both
/// one-hots are present and `None` otherwise (Python can also emit
/// `(None, amt)` for a malformed row with only `Q_lo` set; such rows are
/// never produced by [`expand`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Datapath {
    pub bop: u64,
    pub cin: u64,
    pub cout: bool,
    pub s: u64,
    pub dw: u64,
    pub sp: u64,
    pub x: u64,
    pub and_val: u64,
    pub t0: u64,
    pub t1: u64,
    pub t2: u64,
    pub nw: u64,
    pub eq: bool,
    pub off: u8,
    pub p: [bool; 6],
    pub cond: bool,
    pub y: u64,
    pub gs: u64,
    pub u1: bool,
    pub u2: bool,
    pub cmp: bool,
    pub rdslt: u64,
    pub eqres: u64,
    pub take: bool,
    pub x1: u64,
    pub x2: u64,
    pub x3: u64,
    pub tb: bool,
    pub th: bool,
    pub tw: bool,
    pub m: u64,
    pub l: u64,
    pub rdv: u64,
    pub shift: Option<(u8, u8)>,
}

/// The datapath semantics of one row (spec 9.3; Python `datapath`).
/// `v1 = reg[rs1]`, `v2 = reg[rs2]`, `rw` is the RAM word read.
pub fn datapath(r: &Row, v1: u64, v2: u64, rw: u64) -> Datapath {
    let bop = if r.b_imm { r.imm } else { v2 };
    let bp = bop ^ if r.sub { M64 } else { 0 };
    let mut c = u64::from(r.sub);
    let mut cin = 0u64;
    for i in 0..64 {
        cin |= c << i;
        let (a, b) = (bit(v1, i), bit(bp, i));
        c = (a & b) | (a & c) | (b & c);
    }
    let cout = c == 1;
    let s = v1 ^ bp ^ cin;
    let s31 = bit(s, 31) == 1;
    let dw = if r.w {
        (s ^ if s31 { M64 } else { 0 }) & (M32 << 32)
    } else {
        0
    };
    let sp = s ^ dw;
    let x = v1 ^ bop;
    let and_val = v1 & bop;
    let t0 = if r.c_add { sp } else { 0 };
    let t1 = t0 ^ if r.e { x } else { 0 };
    let t2 = t1 ^ if r.g { and_val } else { 0 };
    let mut nw = 0u64;
    let mut n = bit(s, 0);
    for i in 1..64 {
        n |= bit(s, i);
        nw |= n << i;
    }
    let eq = n == 0;
    let off = (s & 7) as u8;
    let mut p = [false; 6];
    for (k, pk) in p.iter_mut().enumerate() {
        *pk = (r.bsel >> k) & 1 == 1 && bit(v2, k as u32) == 1;
    }
    let mut cond = r.sh_imm;
    for pk in p {
        cond ^= pk;
    }
    let qa = onehot_index(r.q_lo);
    let qk = onehot_index(u64::from(r.q_hi));
    let (y, shift) = match (qa, qk) {
        (Some(a), Some(k)) => (shift_apply(k as u8, a, v1), Some((k as u8, a as u8))),
        _ => (0, None),
    };
    let gs = if cond { sp ^ y } else { 0 };
    let ltu = !cout;
    let u1 = r.f_cmp && ltu;
    let u2 = r.f_lts && (bit(v1, 63) ^ bit(bop, 63) == 1);
    let cmp = u1 ^ u2;
    let rdslt = u64::from(r.g_slt && cmp);
    let eqres = u64::from(r.f_eq && eq);
    let take = r.br && (cmp ^ (eqres == 1) ^ r.inv);
    let x1 = if off & 1 == 1 { rw >> 8 } else { rw };
    let x2 = if off & 2 == 2 { x1 >> 16 } else { x1 };
    let x3 = if off & 4 == 4 { x2 >> 32 } else { x2 };
    let tb = r.ldsb && bit(x3, 7) == 1;
    let th = r.ldsh && bit(x3, 15) == 1;
    let tw = r.ldsw && bit(x3, 31) == 1;
    let m = x3 & lane_mask(r.ln);
    let l = m ^ if tb ^ th ^ tw { lane_mask(r.fill) } else { 0 };
    let rdv = t2 ^ gs ^ l ^ rdslt ^ r.kc;
    Datapath {
        bop,
        cin,
        cout,
        s,
        dw,
        sp,
        x,
        and_val,
        t0,
        t1,
        t2,
        nw,
        eq,
        off,
        p,
        cond,
        y,
        gs,
        u1,
        u2,
        cmp,
        rdslt,
        eqres,
        take,
        x1,
        x2,
        x3,
        tb,
        th,
        tw,
        m,
        l,
        rdv,
        shift,
    }
}

// ---------------------------------------------------------------------------
// Expansion
// ---------------------------------------------------------------------------

/// An expanded program: the bytecode ROM and its derivation data
/// (Python `Program`). The column list is the shared [`COLUMNS`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub rom: Vec<Row>,
    pub upc_of_pc: BTreeMap<u64, u32>,
    pub entry_pc: u64,
    pub entry_upc: u32,
    pub code: BTreeMap<u64, u32>,
    pub cycles_of_pc: BTreeMap<u64, usize>,
}

impl Program {
    /// Python `Program.columns` (always [`COLUMNS`]).
    pub fn columns(&self) -> &'static [Column; 41] {
        &COLUMNS
    }
}

fn imm_alu_base(op: Op) -> Option<Op> {
    Some(match op {
        Op::Addi => Op::Add,
        Op::Slti => Op::Slt,
        Op::Sltiu => Op::Sltu,
        Op::Xori => Op::Xor,
        Op::Ori => Op::Or,
        Op::Andi => Op::And,
        Op::Addiw => Op::Addw,
        _ => return None,
    })
}

fn is_rr_alu(op: Op) -> bool {
    matches!(
        op,
        Op::Add | Op::Sub | Op::Xor | Op::Or | Op::And | Op::Slt | Op::Sltu | Op::Addw | Op::Subw
    )
}

fn shift_imm_kind(op: Op) -> Option<u8> {
    Some(match op {
        Op::Slli => kind::SLL,
        Op::Srli => kind::SRL,
        Op::Srai => kind::SRA,
        Op::Slliw => kind::SLLW,
        Op::Srliw => kind::SRLW,
        Op::Sraiw => kind::SRAW,
        _ => return None,
    })
}

fn shift_reg_kind(op: Op) -> Option<u8> {
    Some(match op {
        Op::Sll => kind::SLL,
        Op::Srl => kind::SRL,
        Op::Sra => kind::SRA,
        Op::Sllw => kind::SLLW,
        Op::Srlw => kind::SRLW,
        Op::Sraw => kind::SRAW,
        _ => return None,
    })
}

fn set_alu_flags(r: &mut Row, op: Op) {
    match op {
        Op::Add | Op::Addw => {
            r.c_add = true;
            r.w = op == Op::Addw;
        }
        Op::Sub | Op::Subw => {
            r.c_add = true;
            r.sub = true;
            r.w = op == Op::Subw;
        }
        Op::Xor => r.e = true,
        Op::Or => {
            r.e = true;
            r.g = true;
        }
        Op::And => r.g = true,
        Op::Slt => {
            r.sub = true;
            r.f_lts = true;
            r.f_cmp = true;
            r.g_slt = true;
        }
        Op::Sltu => {
            r.sub = true;
            r.f_ltu = true;
            r.f_cmp = true;
            r.g_slt = true;
        }
        _ => panic!("_alu_flags: {}", op.name()),
    }
}

/// Rows paired with an explicit `seq` (Python's `_seq` key), if any.
fn expand_instr_inner(i: &Instr, pc: u64, tgt_upc: &dyn Fn(u64) -> u32) -> Vec<(Row, Option<u32>)> {
    let mut rows: Vec<(Row, Option<u32>)> = Vec::new();
    macro_rules! push {
        ($r:expr) => {
            rows.push(($r, None))
        };
    }
    match i.op {
        Op::Illegal | Op::Ebreak => push!(Row {
            trap: true,
            ..Row::default()
        }),
        Op::Ecall => {
            let r = Row {
                ecall: true,
                rs1: 10,
                rs2: 17,
                seq: HALTED_UPC,
                ..Row::default()
            };
            rows.push((r, Some(HALTED_UPC)));
        }
        Op::Fence => push!(Row::default()),
        op if imm_alu_base(op).is_some() || is_rr_alu(op) => {
            if i.rd == 0 {
                push!(Row::default());
            } else {
                let mut r = Row {
                    rs1: i.rs1,
                    rd: i.rd,
                    ..Row::default()
                };
                set_alu_flags(&mut r, imm_alu_base(op).unwrap_or(op));
                if imm_alu_base(op).is_some() {
                    r.b_imm = true;
                    r.imm = i.imm as u64;
                } else {
                    r.rs2 = i.rs2;
                }
                push!(r);
            }
        }
        op if shift_imm_kind(op).is_some() => {
            if i.rd == 0 {
                push!(Row::default());
            } else {
                let k = shift_imm_kind(op).expect("shift imm");
                push!(Row {
                    rs1: i.rs1,
                    rd: i.rd,
                    b_imm: true,
                    c_add: true,
                    sh_imm: true,
                    q_lo: 1u64 << (i.imm as u32),
                    q_hi: 1u8 << k,
                    ..Row::default()
                });
            }
        }
        op if shift_reg_kind(op).is_some() => {
            if i.rd == 0 {
                push!(Row::default());
            } else {
                let k = shift_reg_kind(op).expect("shift reg");
                let word = matches!(k, kind::SLLW | kind::SRLW | kind::SRAW);
                let stages = if word { 5 } else { 6 };
                for s in 0..stages {
                    push!(Row {
                        rs1: if s == 0 { i.rs1 } else { TEMP_REG },
                        rs2: i.rs2,
                        rd: if s == stages - 1 { i.rd } else { TEMP_REG },
                        b_imm: true,
                        c_add: true,
                        w: word,
                        bsel: 1u8 << s,
                        q_lo: 1u64 << (1u32 << s),
                        q_hi: 1u8 << k,
                        ..Row::default()
                    });
                }
            }
        }
        Op::Lui => {
            if i.rd != 0 {
                push!(Row {
                    rd: i.rd,
                    kc: i.imm as u64,
                    ..Row::default()
                });
            } else {
                push!(Row::default());
            }
        }
        Op::Auipc => {
            if i.rd != 0 {
                push!(Row {
                    rd: i.rd,
                    kc: pc.wrapping_add(i.imm as u64),
                    ..Row::default()
                });
            } else {
                push!(Row::default());
            }
        }
        Op::Jal => {
            let r = Row {
                rd: i.rd,
                kc: if i.rd != 0 { pc.wrapping_add(4) } else { 0 },
                ..Row::default()
            };
            let t = tgt_upc(pc.wrapping_add(i.imm as u64));
            rows.push((r, Some(t)));
        }
        Op::Jalr => {
            let r = Row {
                rs1: i.rs1,
                rd: i.rd,
                b_imm: true,
                imm: i.imm as u64,
                kc: if i.rd != 0 { pc.wrapping_add(4) } else { 0 },
                jalr: true,
                ..Row::default()
            };
            rows.push((r, Some(0)));
        }
        op if op.is_branch() => {
            let mut r = Row {
                rs1: i.rs1,
                rs2: i.rs2,
                sub: true,
                br: true,
                tgt: tgt_upc(pc.wrapping_add(i.imm as u64)),
                ..Row::default()
            };
            match op {
                Op::Beq => r.f_eq = true,
                Op::Bne => {
                    r.f_eq = true;
                    r.inv = true;
                }
                Op::Blt => {
                    r.f_lts = true;
                    r.f_cmp = true;
                }
                Op::Bge => {
                    r.f_lts = true;
                    r.f_cmp = true;
                    r.inv = true;
                }
                Op::Bltu => {
                    r.f_ltu = true;
                    r.f_cmp = true;
                }
                _ => {
                    r.f_ltu = true;
                    r.f_cmp = true;
                    r.inv = true;
                }
            }
            push!(r);
        }
        op if op.load_info().is_some() => {
            let (nb, sg) = op.load_info().expect("load");
            let ln = if i.rd == 0 {
                0
            } else {
                ((1u16 << nb) - 1) as u8
            };
            let mut r = Row {
                rs1: i.rs1,
                rd: i.rd,
                b_imm: true,
                imm: i.imm as u64,
                mem: true,
                ln,
                fill: if i.rd != 0 && sg { !ln } else { 0 },
                a_h: nb >= 2,
                a_w: nb >= 4,
                a_d: nb == 8,
                ..Row::default()
            };
            if i.rd != 0 && sg {
                match nb {
                    1 => r.ldsb = true,
                    2 => r.ldsh = true,
                    4 => r.ldsw = true,
                    _ => {}
                }
            }
            push!(r);
        }
        op if op.store_info().is_some() => {
            let nb = op.store_info().expect("store");
            push!(Row {
                rs1: i.rs1,
                rs2: i.rs2,
                b_imm: true,
                imm: i.imm as u64,
                mem: true,
                st_w: 1u8 << (nb.trailing_zeros() as u8),
                a_h: nb >= 2,
                a_w: nb >= 4,
                a_d: nb == 8,
                ..Row::default()
            });
        }
        // Python raises AssertionError here; every Op is covered above.
        op => unreachable!("expand_instr: {op:?}"),
    }
    rows
}

/// Rows for one instruction (Python `expand_instr`), spec table 9.4.
/// `tgt_upc(pc)` returns the head micro-PC of an RV64I pc or [`TRAP_UPC`].
/// Rows carry no `upc`/`rpc`/`head`; `seq` holds Python's explicit `_seq`
/// where one exists (JAL target, ECALL→HALTED, JALR→0) and 0 otherwise.
/// [`expand`] fills in the rest.
pub fn expand_instr(i: &Instr, pc: u64, tgt_upc: &dyn Fn(u64) -> u32) -> Vec<Row> {
    expand_instr_inner(i, pc, tgt_upc)
        .into_iter()
        .map(|(mut r, sq)| {
            if let Some(s) = sq {
                r.seq = s;
            }
            r
        })
        .collect()
}

/// Expand a whole code image into a [`Program`] (spec 9.7; Python
/// `expand`). Deterministic in `(code, entry_pc)`: `HALTED = 0`,
/// `TRAP = 1`, then instruction rows in ascending pc, each instruction's
/// rows contiguous.
///
/// # Panics
/// If `entry_pc` is not in `code`, matching Python's `assert`.
pub fn expand(code: &BTreeMap<u64, u32>, entry_pc: u64) -> Program {
    let instrs: BTreeMap<u64, Instr> = code.iter().map(|(&pc, &w)| (pc, decode(w))).collect();
    let counts: BTreeMap<u64, usize> = instrs
        .iter()
        .map(|(&pc, i)| (pc, expand_instr_inner(i, pc, &|_| TRAP_UPC).len()))
        .collect();
    let mut upc_of_pc: BTreeMap<u64, u32> = BTreeMap::new();
    let mut nxt: u32 = 2;
    for &pc in instrs.keys() {
        upc_of_pc.insert(pc, nxt);
        nxt += counts[&pc] as u32;
    }
    let tgt_upc = |p: u64| -> u32 {
        if p.is_multiple_of(4) {
            upc_of_pc.get(&p).copied().unwrap_or(TRAP_UPC)
        } else {
            TRAP_UPC
        }
    };
    let mut rom = vec![
        Row {
            upc: HALTED_UPC,
            halted: true,
            rs1: 10,
            seq: HALTED_UPC,
            ..Row::default()
        },
        Row {
            upc: TRAP_UPC,
            trap: true,
            seq: TRAP_UPC,
            ..Row::default()
        },
    ];
    for (&pc, i) in &instrs {
        let rows = expand_instr_inner(i, pc, &tgt_upc);
        let n = rows.len();
        for (k, (mut r, sq)) in rows.into_iter().enumerate() {
            let u = rom.len() as u32;
            r.upc = u;
            r.rpc = pc;
            r.head = k == 0;
            r.seq = match sq {
                Some(s) => s,
                None if k + 1 < n => u + 1,
                None => tgt_upc(pc.wrapping_add(4)),
            };
            rom.push(r);
        }
    }
    assert_eq!(rom.len() as u32, nxt);
    let &entry_upc = upc_of_pc.get(&entry_pc).expect("entry pc not in code");
    Program {
        rom,
        upc_of_pc,
        entry_pc,
        entry_upc,
        code: code.clone(),
        cycles_of_pc: counts,
    }
}

// ---------------------------------------------------------------------------
// Virtual machine
// ---------------------------------------------------------------------------

/// One executed virtual cycle (Python trace record dict). `inc` is the
/// RAM increment `ram_old ^ ram_new`; `dynu` is the dynamic target
/// micro-PC on `JALR` rows and 0 otherwise; `dp` holds all datapath
/// intermediates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceRecord {
    pub upc: u32,
    pub rom: Row,
    pub rs1: u8,
    pub rs2: u8,
    pub rd: u8,
    pub v1: u64,
    pub v2: u64,
    pub rd_old: u64,
    pub rd_val: u64,
    pub ram_idx: usize,
    pub ram_old: u64,
    pub ram_new: u64,
    pub inc: u64,
    pub shift_kind: Option<u8>,
    pub shift_amt: Option<u8>,
    pub shift_src: u64,
    pub shift_out: u64,
    pub store_width: Option<u8>,
    pub store_off: u8,
    pub store_src: u64,
    pub take: bool,
    pub dynu: u32,
    pub next_upc: u32,
    pub dp: Datapath,
}

/// Result of a virtual execution (Python `VMResult`). `regs` has 64
/// entries (32 architectural + 32 virtual); `instret` counts RV64I
/// instructions retired (heads executed, HALT included).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VMResult {
    pub exit_code: u64,
    pub regs: [u64; 64],
    pub ram: BTreeMap<usize, u64>,
    pub trace: Vec<TraceRecord>,
    pub instret: u64,
}

/// The virtual machine: executes ROM rows from `entry_upc` until the
/// `HALTED` row (Python `VirtualMachine`).
pub struct VirtualMachine {
    pub program: Program,
    pub ram: BTreeMap<usize, u64>,
    /// `A`: RAM holds `2^A` words.
    pub ram_log_words: u32,
    pub regs: [u64; 64],
    pub upc: u32,
}

impl VirtualMachine {
    pub fn new(program: Program, ram_words: &BTreeMap<usize, u64>, ram_log_words: u32) -> Self {
        let upc = program.entry_upc;
        VirtualMachine {
            program,
            ram: ram_words
                .iter()
                .filter(|&(_, &v)| v != 0)
                .map(|(&k, &v)| (k, v))
                .collect(),
            ram_log_words,
            regs: [0; 64],
            upc,
        }
    }

    /// Run until the `HALTED` row is reached (it is not executed), at
    /// most `max_cycles` virtual cycles.
    pub fn run(&mut self, max_cycles: usize) -> Result<VMResult, Trap> {
        let mut trace: Vec<TraceRecord> = Vec::new();
        let mut instret: u64 = 0;
        loop {
            let row = self.program.rom[self.upc as usize];
            if row.halted {
                break;
            }
            if trace.len() >= max_cycles {
                return Err(Trap::MaxCyclesExceeded);
            }
            instret += u64::from(row.head);
            trace.push(self.step(&row)?);
        }
        Ok(VMResult {
            exit_code: self.regs[10],
            regs: self.regs,
            ram: self.ram.clone(),
            trace,
            instret,
        })
    }

    /// Run to HALT, then append `HALTED` cycles until the trace length
    /// is a power of two >= 4 that exceeds the number of real cycles
    /// (so the final cycle is `HALTED`).
    pub fn run_padded(&mut self, max_cycles: usize) -> Result<VMResult, Trap> {
        let mut res = self.run(max_cycles)?;
        let mut t = 4usize;
        while t < res.trace.len() + 1 {
            t *= 2;
        }
        while res.trace.len() < t {
            let halted = self.program.rom[HALTED_UPC as usize];
            res.trace.push(self.step(&halted)?);
        }
        Ok(res)
    }

    /// Execute one virtual cycle for `row` (Python `VirtualMachine.step`).
    pub fn step(&mut self, row: &Row) -> Result<TraceRecord, Trap> {
        let row = *row;
        if row.trap {
            return Err(Trap::TrapRow);
        }
        let mut v1 = self.regs[row.rs1 as usize];
        let mut v2 = self.regs[row.rs2 as usize];
        if row.rs1 == 0 {
            v1 = 0;
        }
        if row.rs2 == 0 {
            v2 = 0;
        }
        if row.ecall && v2 != 0 {
            return Err(Trap::UnsupportedEcall);
        }
        // RAM read (word 0 when no access). The address is the adder
        // output, which does not depend on the word read.
        let s0 = datapath(&row, v1, v2, 0).s;
        let mut ridx = 0usize;
        if row.mem {
            if (row.a_h && s0 & 1 != 0) || (row.a_w && s0 & 2 != 0) || (row.a_d && s0 & 4 != 0) {
                return Err(Trap::MisalignedAccess { addr: s0 });
            }
            let off = s0.wrapping_sub(RAM_BASE);
            if off >= (8u64 << self.ram_log_words) {
                return Err(Trap::AccessOutOfRange { addr: s0 });
            }
            ridx = (off >> 3) as usize;
        }
        let rw = self.ram.get(&ridx).copied().unwrap_or(0);
        let d = datapath(&row, v1, v2, rw);
        let rdv = d.rdv;
        let rd = row.rd;
        let rd_old = self.regs[rd as usize];
        if rd == 0 {
            assert_eq!(rdv, 0, "x0 write must be zero");
        }
        let new = if row.st_w != 0 {
            store_apply(
                onehot_index(u64::from(row.st_w)).expect("st_w one-hot") as u8,
                u32::from(d.off),
                rw,
                v2,
            )
        } else {
            rw
        };
        if new != 0 {
            self.ram.insert(ridx, new);
        } else {
            self.ram.remove(&ridx);
        }
        self.regs[rd as usize] = rdv;
        self.regs[0] = 0;
        let (dynu, nxt) = if row.jalr {
            let target = d.s & !1;
            let dynu = self
                .program
                .upc_of_pc
                .get(&target)
                .copied()
                .ok_or(Trap::JalrToNonCode { target })?;
            (dynu, dynu)
        } else {
            (0, if d.take { row.tgt } else { row.seq })
        };
        let rec = TraceRecord {
            upc: row.upc,
            rom: row,
            rs1: row.rs1,
            rs2: row.rs2,
            rd,
            v1,
            v2,
            rd_old,
            rd_val: rdv,
            ram_idx: ridx,
            ram_old: rw,
            ram_new: new,
            inc: rw ^ new,
            shift_kind: onehot_index(u64::from(row.q_hi)).map(|k| k as u8),
            shift_amt: onehot_index(row.q_lo).map(|a| a as u8),
            shift_src: v1,
            shift_out: d.y,
            store_width: onehot_index(u64::from(row.st_w)).map(|w| w as u8),
            store_off: d.off,
            store_src: v2,
            take: d.take,
            dynu: if row.jalr { dynu } else { 0 },
            next_upc: nxt,
            dp: d,
        };
        self.upc = nxt;
        Ok(rec)
    }
}

/// Expand and run a program to HALT (Python `run_program`).
pub fn run_program(
    code: &BTreeMap<u64, u32>,
    entry_pc: u64,
    ram_words: &BTreeMap<usize, u64>,
    ram_log_words: u32,
    max_cycles: usize,
) -> Result<VMResult, Trap> {
    VirtualMachine::new(expand(code, entry_pc), ram_words, ram_log_words).run(max_cycles)
}
