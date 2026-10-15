//! RV64I decoder and plain reference interpreter (the oracle).
//!
//! Mirrors `reference/openmagnetar/riscv.py`. Semantics follow *The RISC-V
//! Instruction Set Manual, Volume I: Unprivileged ISA* (RV64I base).
//! Machine model per CONVENTIONS C5/C6; conditions C5/C6 declare
//! "unprovable" return [`Trap`].

use std::collections::BTreeMap;
use std::fmt;

pub const M64: u64 = u64::MAX;
pub const M32: u64 = 0xFFFF_FFFF;
pub const RAM_BASE: u64 = 0x8000_0000;

/// An unprovable condition (Python `Trap`): illegal encoding, `EBREAK`,
/// unsupported `ECALL`, misaligned or out-of-range access, bad fetch or
/// jump target, or the cycle budget being exceeded. A prover must not
/// produce a proof for an execution that ends in any of these.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Trap {
    /// Illegal or unsupported encoding at `pc` (Python `ILLEGAL at …`).
    Illegal { pc: u64 },
    /// `EBREAK` at `pc`.
    Ebreak { pc: u64 },
    /// `ECALL` with `a7 != 0`.
    UnsupportedEcall,
    /// Misaligned load/store at byte address `addr`.
    MisalignedAccess { addr: u64 },
    /// Load/store outside `[RAM_BASE, RAM_BASE + 8 * 2^A)`.
    AccessOutOfRange { addr: u64 },
    /// Fetch from a pc not in the code image.
    Fetch { pc: u64 },
    /// Jump/branch target not 4-aligned.
    MisalignedJumpTarget,
    /// `max_cycles` exceeded before HALT.
    MaxCyclesExceeded,
    /// Virtual machine reached a `TRAP` ROM row.
    TrapRow,
    /// `JALR` target with no head row in the code image.
    JalrToNonCode { target: u64 },
}

impl fmt::Display for Trap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Trap::Illegal { pc } => write!(f, "ILLEGAL at {pc:#x}"),
            Trap::Ebreak { pc } => write!(f, "EBREAK at {pc:#x}"),
            Trap::UnsupportedEcall => write!(f, "unsupported ECALL"),
            Trap::MisalignedAccess { addr } => write!(f, "misaligned access at {addr:#x}"),
            Trap::AccessOutOfRange { addr } => write!(f, "access out of range at {addr:#x}"),
            Trap::Fetch { pc } => write!(f, "fetch from {pc:#x}"),
            Trap::MisalignedJumpTarget => write!(f, "misaligned jump target"),
            Trap::MaxCyclesExceeded => write!(f, "max_cycles exceeded"),
            Trap::TrapRow => write!(f, "trap row reached"),
            Trap::JalrToNonCode { target } => write!(f, "jalr to non-code pc {target:#x}"),
        }
    }
}

impl std::error::Error for Trap {}

/// Sign-extend the low `bits` of `x` (Python `sext`). `bits` must be in
/// `1..=64`.
pub fn sext(x: u64, bits: u32) -> i64 {
    debug_assert!((1..=64).contains(&bits));
    let shift = 64 - bits;
    ((x << shift) as i64) >> shift
}

/// Sign-extension of bits 31..0 as a `u64` (spec `sext32`).
pub fn sext32(x: u64) -> u64 {
    sext(x & M32, 32) as u64
}

/// The two's-complement view of a `u64` (Python `s64`).
pub fn s64(x: u64) -> i64 {
    x as i64
}

/// RV64I mnemonics, plus `Illegal` for anything outside strict RV64I.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    Illegal,
    Lui,
    Auipc,
    Jal,
    Jalr,
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,
    Lb,
    Lh,
    Lw,
    Ld,
    Lbu,
    Lhu,
    Lwu,
    Sb,
    Sh,
    Sw,
    Sd,
    Addi,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
    Slli,
    Srli,
    Srai,
    Addiw,
    Slliw,
    Srliw,
    Sraiw,
    Add,
    Sub,
    Sll,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,
    Addw,
    Subw,
    Sllw,
    Srlw,
    Sraw,
    Fence,
    Ecall,
    Ebreak,
}

impl Op {
    /// Upper-case mnemonic, exactly Python's `Instr.name`.
    pub fn name(self) -> &'static str {
        match self {
            Op::Illegal => "ILLEGAL",
            Op::Lui => "LUI",
            Op::Auipc => "AUIPC",
            Op::Jal => "JAL",
            Op::Jalr => "JALR",
            Op::Beq => "BEQ",
            Op::Bne => "BNE",
            Op::Blt => "BLT",
            Op::Bge => "BGE",
            Op::Bltu => "BLTU",
            Op::Bgeu => "BGEU",
            Op::Lb => "LB",
            Op::Lh => "LH",
            Op::Lw => "LW",
            Op::Ld => "LD",
            Op::Lbu => "LBU",
            Op::Lhu => "LHU",
            Op::Lwu => "LWU",
            Op::Sb => "SB",
            Op::Sh => "SH",
            Op::Sw => "SW",
            Op::Sd => "SD",
            Op::Addi => "ADDI",
            Op::Slti => "SLTI",
            Op::Sltiu => "SLTIU",
            Op::Xori => "XORI",
            Op::Ori => "ORI",
            Op::Andi => "ANDI",
            Op::Slli => "SLLI",
            Op::Srli => "SRLI",
            Op::Srai => "SRAI",
            Op::Addiw => "ADDIW",
            Op::Slliw => "SLLIW",
            Op::Srliw => "SRLIW",
            Op::Sraiw => "SRAIW",
            Op::Add => "ADD",
            Op::Sub => "SUB",
            Op::Sll => "SLL",
            Op::Slt => "SLT",
            Op::Sltu => "SLTU",
            Op::Xor => "XOR",
            Op::Srl => "SRL",
            Op::Sra => "SRA",
            Op::Or => "OR",
            Op::And => "AND",
            Op::Addw => "ADDW",
            Op::Subw => "SUBW",
            Op::Sllw => "SLLW",
            Op::Srlw => "SRLW",
            Op::Sraw => "SRAW",
            Op::Fence => "FENCE",
            Op::Ecall => "ECALL",
            Op::Ebreak => "EBREAK",
        }
    }

    /// Python `LOAD_INFO[name]`: `(nbytes, signed)` for loads.
    pub fn load_info(self) -> Option<(usize, bool)> {
        match self {
            Op::Lb => Some((1, true)),
            Op::Lh => Some((2, true)),
            Op::Lw => Some((4, true)),
            Op::Ld => Some((8, false)),
            Op::Lbu => Some((1, false)),
            Op::Lhu => Some((2, false)),
            Op::Lwu => Some((4, false)),
            _ => None,
        }
    }

    /// Python `STORE_INFO[name]`: width in bytes for stores.
    pub fn store_info(self) -> Option<usize> {
        match self {
            Op::Sb => Some(1),
            Op::Sh => Some(2),
            Op::Sw => Some(4),
            Op::Sd => Some(8),
            _ => None,
        }
    }

    pub fn is_branch(self) -> bool {
        matches!(
            self,
            Op::Beq | Op::Bne | Op::Blt | Op::Bge | Op::Bltu | Op::Bgeu
        )
    }

    /// True for the OP-IMM / OP-IMM-32 ALU ops whose B operand is `imm`
    /// (the `imm_ops` set of Python `Machine.step`).
    pub fn is_imm_alu(self) -> bool {
        matches!(
            self,
            Op::Addi
                | Op::Slti
                | Op::Sltiu
                | Op::Xori
                | Op::Ori
                | Op::Andi
                | Op::Slli
                | Op::Srli
                | Op::Srai
                | Op::Addiw
                | Op::Slliw
                | Op::Srliw
                | Op::Sraiw
        )
    }
}

/// A decoded instruction (Python `Instr`). `imm` is the signed immediate
/// (shamt for shifts; for U-type, `imm20 << 12` sign-extended from 32 bits).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instr {
    pub op: Op,
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub imm: i64,
    pub word: u32,
}

impl Instr {
    /// Python `Instr.name`.
    pub fn name(&self) -> &'static str {
        self.op.name()
    }
}

/// Decode one 32-bit instruction word, exactly as Python `riscv.decode`.
/// Anything outside strict RV64I (M/A/F/D/C extensions, CSR, `FENCE.I`,
/// reserved funct fields) decodes to [`Op::Illegal`].
pub fn decode(word: u32) -> Instr {
    let w = word;
    let bad = Instr {
        op: Op::Illegal,
        rd: 0,
        rs1: 0,
        rs2: 0,
        imm: 0,
        word: w,
    };
    let opc = w & 0x7F;
    let rd = ((w >> 7) & 31) as u8;
    let f3 = (w >> 12) & 7;
    let rs1 = ((w >> 15) & 31) as u8;
    let rs2 = ((w >> 20) & 31) as u8;
    let f7 = (w >> 25) & 0x7F;
    let imm_i = sext((w >> 20) as u64, 12);
    let imm_s = sext((((w >> 25) << 5) | ((w >> 7) & 31)) as u64, 12);
    let imm_b = sext(
        (((w >> 31) << 12)
            | (((w >> 7) & 1) << 11)
            | (((w >> 25) & 0x3F) << 5)
            | (((w >> 8) & 0xF) << 1)) as u64,
        13,
    );
    let imm_u = sext((w & 0xFFFF_F000) as u64, 32);
    let imm_j = sext(
        (((w >> 31) << 20)
            | (((w >> 12) & 0xFF) << 12)
            | (((w >> 20) & 1) << 11)
            | (((w >> 21) & 0x3FF) << 1)) as u64,
        21,
    );
    let mk = |op, rd, rs1, rs2, imm| Instr {
        op,
        rd,
        rs1,
        rs2,
        imm,
        word: w,
    };
    match opc {
        0x37 => mk(Op::Lui, rd, 0, 0, imm_u),
        0x17 => mk(Op::Auipc, rd, 0, 0, imm_u),
        0x6F => mk(Op::Jal, rd, 0, 0, imm_j),
        0x67 => {
            if f3 == 0 {
                mk(Op::Jalr, rd, rs1, 0, imm_i)
            } else {
                bad
            }
        }
        0x63 => {
            let op = match f3 {
                0 => Op::Beq,
                1 => Op::Bne,
                4 => Op::Blt,
                5 => Op::Bge,
                6 => Op::Bltu,
                7 => Op::Bgeu,
                _ => return bad,
            };
            mk(op, 0, rs1, rs2, imm_b)
        }
        0x03 => {
            let op = match f3 {
                0 => Op::Lb,
                1 => Op::Lh,
                2 => Op::Lw,
                3 => Op::Ld,
                4 => Op::Lbu,
                5 => Op::Lhu,
                6 => Op::Lwu,
                _ => return bad,
            };
            mk(op, rd, rs1, 0, imm_i)
        }
        0x23 => {
            let op = match f3 {
                0 => Op::Sb,
                1 => Op::Sh,
                2 => Op::Sw,
                3 => Op::Sd,
                _ => return bad,
            };
            mk(op, 0, rs1, rs2, imm_s)
        }
        0x13 => {
            let shamt = i64::from((w >> 20) & 0x3F);
            let f6 = w >> 26;
            match f3 {
                0 => mk(Op::Addi, rd, rs1, 0, imm_i),
                2 => mk(Op::Slti, rd, rs1, 0, imm_i),
                3 => mk(Op::Sltiu, rd, rs1, 0, imm_i),
                4 => mk(Op::Xori, rd, rs1, 0, imm_i),
                6 => mk(Op::Ori, rd, rs1, 0, imm_i),
                7 => mk(Op::Andi, rd, rs1, 0, imm_i),
                1 if f6 == 0 => mk(Op::Slli, rd, rs1, 0, shamt),
                5 if f6 == 0 => mk(Op::Srli, rd, rs1, 0, shamt),
                5 if f6 == 0x10 => mk(Op::Srai, rd, rs1, 0, shamt),
                _ => bad,
            }
        }
        0x1B => {
            // Python puts the 5-bit shamt in `imm` via the rs2 field; bit 25
            // is thus forced 0 by the f7 checks.
            let shamt = i64::from(rs2);
            match f3 {
                0 => mk(Op::Addiw, rd, rs1, 0, imm_i),
                1 if f7 == 0 => mk(Op::Slliw, rd, rs1, 0, shamt),
                5 if f7 == 0 => mk(Op::Srliw, rd, rs1, 0, shamt),
                5 if f7 == 0x20 => mk(Op::Sraiw, rd, rs1, 0, shamt),
                _ => bad,
            }
        }
        0x33 => {
            let op = match (f7, f3) {
                (0, 0) => Op::Add,
                (0x20, 0) => Op::Sub,
                (0, 1) => Op::Sll,
                (0, 2) => Op::Slt,
                (0, 3) => Op::Sltu,
                (0, 4) => Op::Xor,
                (0, 5) => Op::Srl,
                (0x20, 5) => Op::Sra,
                (0, 6) => Op::Or,
                (0, 7) => Op::And,
                _ => return bad,
            };
            mk(op, rd, rs1, rs2, 0)
        }
        0x3B => {
            let op = match (f7, f3) {
                (0, 0) => Op::Addw,
                (0x20, 0) => Op::Subw,
                (0, 1) => Op::Sllw,
                (0, 5) => Op::Srlw,
                (0x20, 5) => Op::Sraw,
                _ => return bad,
            };
            mk(op, rd, rs1, rs2, 0)
        }
        // FENCE.I (f3=1) is Zifencei: illegal.
        0x0F => {
            if f3 == 0 {
                mk(Op::Fence, 0, 0, 0, 0)
            } else {
                bad
            }
        }
        0x73 => match w {
            0x0000_0073 => mk(Op::Ecall, 0, 0, 0, 0),
            0x0010_0073 => mk(Op::Ebreak, 0, 0, 0, 0),
            _ => bad,
        },
        _ => bad,
    }
}

/// Register/immediate ALU operations on `u64` inputs (Python `riscv.alu`).
///
/// # Panics
/// On a non-ALU `op`, matching Python's `ValueError` programmer error.
pub fn alu(op: Op, a: u64, b: u64) -> u64 {
    let sh = (b & 63) as u32;
    let shw = (b & 31) as u32;
    match op {
        Op::Add | Op::Addi => a.wrapping_add(b),
        Op::Sub => a.wrapping_sub(b),
        Op::Xor | Op::Xori => a ^ b,
        Op::Or | Op::Ori => a | b,
        Op::And | Op::Andi => a & b,
        Op::Slt | Op::Slti => u64::from(s64(a) < s64(b)),
        Op::Sltu | Op::Sltiu => u64::from(a < b),
        Op::Sll | Op::Slli => a << sh,
        Op::Srl | Op::Srli => a >> sh,
        Op::Sra | Op::Srai => (s64(a) >> sh) as u64,
        Op::Addw | Op::Addiw => sext32(a.wrapping_add(b)),
        Op::Subw => sext32(a.wrapping_sub(b)),
        Op::Sllw | Op::Slliw => sext32((a << shw) & M32),
        Op::Srlw | Op::Srliw => sext32((a & M32) >> shw),
        Op::Sraw | Op::Sraiw => (sext(a & M32, 32) >> shw) as u64,
        _ => panic!("alu: not an ALU op: {}", op.name()),
    }
}

/// Result of a halted plain execution (Python `ExecResult`). `ram` maps
/// word index to word value and holds no zero words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecResult {
    pub exit_code: u64,
    pub regs: [u64; 32],
    pub ram: BTreeMap<usize, u64>,
    pub instret: u64,
}

/// Plain RV64I interpreter over `(code, entry_pc, ram_words)`; the oracle.
pub struct Machine {
    pub code: BTreeMap<u64, u32>,
    pub pc: u64,
    pub ram: BTreeMap<usize, u64>,
    /// `A`: RAM holds `2^A` words.
    pub ram_log_words: u32,
    pub regs: [u64; 32],
    pub instret: u64,
}

impl Machine {
    pub fn new(
        code: BTreeMap<u64, u32>,
        entry_pc: u64,
        ram_words: &BTreeMap<usize, u64>,
        ram_log_words: u32,
    ) -> Self {
        Machine {
            code,
            pc: entry_pc,
            ram: ram_words
                .iter()
                .filter(|&(_, &v)| v != 0)
                .map(|(&k, &v)| (k, v))
                .collect(),
            ram_log_words,
            regs: [0; 32],
            instret: 0,
        }
    }

    fn widx(&self, addr: u64, nbytes: usize) -> Result<(usize, usize), Trap> {
        if addr & (nbytes as u64 - 1) != 0 {
            return Err(Trap::MisalignedAccess { addr });
        }
        let off = addr.wrapping_sub(RAM_BASE);
        if off >= (8u64 << self.ram_log_words) {
            return Err(Trap::AccessOutOfRange { addr });
        }
        Ok(((off >> 3) as usize, (off & 7) as usize))
    }

    pub fn load(&self, addr: u64, nbytes: usize, signed: bool) -> Result<u64, Trap> {
        let (idx, off) = self.widx(addr, nbytes)?;
        let mask: u64 = if nbytes == 8 {
            M64
        } else {
            (1u64 << (8 * nbytes)) - 1
        };
        let v = (self.ram.get(&idx).copied().unwrap_or(0) >> (8 * off)) & mask;
        Ok(if signed {
            sext(v, (8 * nbytes) as u32) as u64
        } else {
            v
        })
    }

    pub fn store(&mut self, addr: u64, nbytes: usize, val: u64) -> Result<(), Trap> {
        let (idx, off) = self.widx(addr, nbytes)?;
        let field: u64 = if nbytes == 8 {
            M64
        } else {
            (1u64 << (8 * nbytes)) - 1
        };
        let mask = field << (8 * off);
        let old = self.ram.get(&idx).copied().unwrap_or(0);
        let new = (old & !mask) | ((val << (8 * off)) & mask);
        if new != 0 {
            self.ram.insert(idx, new);
        } else {
            self.ram.remove(&idx);
        }
        Ok(())
    }

    fn wr(&mut self, rd: u8, v: u64) {
        if rd != 0 {
            self.regs[rd as usize] = v;
        }
    }

    /// Execute one instruction. Returns `Some(exit_code)` on HALT.
    pub fn step(&mut self) -> Result<Option<u64>, Trap> {
        let pc = self.pc;
        let word = self.code.get(&pc).copied().ok_or(Trap::Fetch { pc })?;
        let i = decode(word);
        let r = self.regs;
        let mut nxt = pc.wrapping_add(4);
        match i.op {
            Op::Illegal => return Err(Trap::Illegal { pc }),
            Op::Ebreak => return Err(Trap::Ebreak { pc }),
            Op::Lui => self.wr(i.rd, i.imm as u64),
            Op::Auipc => {
                let v = pc.wrapping_add(i.imm as u64);
                self.wr(i.rd, v);
            }
            Op::Jal => {
                self.wr(i.rd, pc.wrapping_add(4));
                nxt = pc.wrapping_add(i.imm as u64);
            }
            Op::Jalr => {
                let t = r[i.rs1 as usize].wrapping_add(i.imm as u64) & !1;
                self.wr(i.rd, pc.wrapping_add(4));
                nxt = t;
            }
            Op::Beq | Op::Bne | Op::Blt | Op::Bge | Op::Bltu | Op::Bgeu => {
                let (a, b) = (r[i.rs1 as usize], r[i.rs2 as usize]);
                let take = match i.op {
                    Op::Beq => a == b,
                    Op::Bne => a != b,
                    Op::Blt => s64(a) < s64(b),
                    Op::Bge => s64(a) >= s64(b),
                    Op::Bltu => a < b,
                    _ => a >= b,
                };
                if take {
                    nxt = pc.wrapping_add(i.imm as u64);
                }
            }
            Op::Fence => {}
            Op::Ecall => {
                if r[17] != 0 {
                    return Err(Trap::UnsupportedEcall);
                }
                self.instret += 1;
                return Ok(Some(r[10]));
            }
            op => {
                if let Some((nb, sg)) = op.load_info() {
                    let addr = r[i.rs1 as usize].wrapping_add(i.imm as u64);
                    let v = self.load(addr, nb, sg)?;
                    self.wr(i.rd, v);
                } else if let Some(nb) = op.store_info() {
                    let addr = r[i.rs1 as usize].wrapping_add(i.imm as u64);
                    self.store(addr, nb, r[i.rs2 as usize])?;
                } else {
                    let b = if op.is_imm_alu() {
                        i.imm as u64
                    } else {
                        r[i.rs2 as usize]
                    };
                    let v = alu(op, r[i.rs1 as usize], b);
                    self.wr(i.rd, v);
                }
            }
        }
        if nxt & 3 != 0 {
            return Err(Trap::MisalignedJumpTarget);
        }
        self.pc = nxt;
        self.instret += 1;
        Ok(None)
    }

    /// Run until HALT, at most `max_cycles` instructions.
    pub fn run(&mut self, max_cycles: usize) -> Result<ExecResult, Trap> {
        for _ in 0..max_cycles {
            if let Some(ec) = self.step()? {
                return Ok(ExecResult {
                    exit_code: ec,
                    regs: self.regs,
                    ram: self.ram.clone(),
                    instret: self.instret,
                });
            }
        }
        Err(Trap::MaxCyclesExceeded)
    }
}
