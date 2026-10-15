//! Tiny RV64I assembler for tests, ported from `reference/tests/asm.py`.
#![allow(dead_code)]

use std::collections::BTreeMap;

fn r(f7: u32, rs2: u32, rs1: u32, f3: u32, rd: u32, opc: u32) -> u32 {
    (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opc
}
fn i(imm: i64, rs1: u32, f3: u32, rd: u32, opc: u32) -> u32 {
    (((imm as u32) & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opc
}
fn s(imm: i64, rs2: u32, rs1: u32, f3: u32) -> u32 {
    let imm = (imm as u32) & 0xFFF;
    ((imm >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((imm & 31) << 7) | 0x23
}
fn b(imm: i64, rs2: u32, rs1: u32, f3: u32) -> u32 {
    let imm = (imm as u32) & 0x1FFF;
    (((imm >> 12) & 1) << 31)
        | (((imm >> 5) & 0x3F) << 25)
        | (rs2 << 20)
        | (rs1 << 15)
        | (f3 << 12)
        | (((imm >> 1) & 0xF) << 8)
        | (((imm >> 11) & 1) << 7)
        | 0x63
}
fn u(imm20: u32, rd: u32, opc: u32) -> u32 {
    ((imm20 & 0xFFFFF) << 12) | (rd << 7) | opc
}
fn j(imm: i64, rd: u32) -> u32 {
    let imm = (imm as u32) & 0x1F_FFFF;
    (((imm >> 20) & 1) << 31)
        | (((imm >> 1) & 0x3FF) << 21)
        | (((imm >> 11) & 1) << 20)
        | (((imm >> 12) & 0xFF) << 12)
        | (rd << 7)
        | 0x6F
}

macro_rules! op_i {
    ($name:ident, $f3:expr) => {
        pub fn $name(rd: u32, rs1: u32, imm: i64) -> u32 {
            i(imm, rs1, $f3, rd, 0x13)
        }
    };
}
op_i!(addi, 0);
op_i!(slti, 2);
op_i!(sltiu, 3);
op_i!(xori, 4);
op_i!(ori, 6);
op_i!(andi, 7);

macro_rules! op_r {
    ($name:ident, $f7:expr, $f3:expr, $opc:expr) => {
        pub fn $name(rd: u32, rs1: u32, rs2: u32) -> u32 {
            r($f7, rs2, rs1, $f3, rd, $opc)
        }
    };
}
op_r!(add, 0, 0, 0x33);
op_r!(sub, 0x20, 0, 0x33);
op_r!(sll, 0, 1, 0x33);
op_r!(slt, 0, 2, 0x33);
op_r!(sltu, 0, 3, 0x33);
op_r!(xor, 0, 4, 0x33);
op_r!(srl, 0, 5, 0x33);
op_r!(sra, 0x20, 5, 0x33);
op_r!(or_, 0, 6, 0x33);
op_r!(and_, 0, 7, 0x33);
op_r!(addw, 0, 0, 0x3B);
op_r!(subw, 0x20, 0, 0x3B);
op_r!(sllw, 0, 1, 0x3B);
op_r!(srlw, 0, 5, 0x3B);
op_r!(sraw, 0x20, 5, 0x3B);

pub fn slli(rd: u32, rs1: u32, sh: i64) -> u32 {
    i(sh, rs1, 1, rd, 0x13)
}
pub fn srli(rd: u32, rs1: u32, sh: i64) -> u32 {
    i(sh, rs1, 5, rd, 0x13)
}
pub fn srai(rd: u32, rs1: u32, sh: i64) -> u32 {
    i((0x10 << 6) | sh, rs1, 5, rd, 0x13)
}
pub fn addiw(rd: u32, rs1: u32, imm: i64) -> u32 {
    i(imm, rs1, 0, rd, 0x1B)
}
pub fn slliw(rd: u32, rs1: u32, sh: i64) -> u32 {
    i(sh, rs1, 1, rd, 0x1B)
}
pub fn srliw(rd: u32, rs1: u32, sh: i64) -> u32 {
    i(sh, rs1, 5, rd, 0x1B)
}
pub fn sraiw(rd: u32, rs1: u32, sh: i64) -> u32 {
    i((0x20 << 5) | sh, rs1, 5, rd, 0x1B)
}

macro_rules! op_b {
    ($name:ident, $f3:expr) => {
        pub fn $name(rs1: u32, rs2: u32, off: i64) -> u32 {
            b(off, rs2, rs1, $f3)
        }
    };
}
op_b!(beq, 0);
op_b!(bne, 1);
op_b!(blt, 4);
op_b!(bge, 5);
op_b!(bltu, 6);
op_b!(bgeu, 7);

macro_rules! op_ld {
    ($name:ident, $f3:expr) => {
        pub fn $name(rd: u32, rs1: u32, imm: i64) -> u32 {
            i(imm, rs1, $f3, rd, 0x03)
        }
    };
}
op_ld!(lb, 0);
op_ld!(lh, 1);
op_ld!(lw, 2);
op_ld!(ld, 3);
op_ld!(lbu, 4);
op_ld!(lhu, 5);
op_ld!(lwu, 6);

macro_rules! op_st {
    ($name:ident, $f3:expr) => {
        pub fn $name(rs2: u32, rs1: u32, imm: i64) -> u32 {
            s(imm, rs2, rs1, $f3)
        }
    };
}
op_st!(sb, 0);
op_st!(sh, 1);
op_st!(sw, 2);
op_st!(sd, 3);

pub fn lui(rd: u32, imm20: u32) -> u32 {
    u(imm20, rd, 0x37)
}
pub fn auipc(rd: u32, imm20: u32) -> u32 {
    u(imm20, rd, 0x17)
}
pub fn jal(rd: u32, off: i64) -> u32 {
    j(off, rd)
}
pub fn jalr(rd: u32, rs1: u32, imm: i64) -> u32 {
    i(imm, rs1, 0, rd, 0x67)
}
pub fn fence() -> u32 {
    0x0FF0_000F
}
pub fn ecall() -> u32 {
    0x73
}
pub fn ebreak() -> u32 {
    0x0010_0073
}

/// `(code, entry_pc)` at base 0x1000, as Python `program()`.
pub fn program(instrs: &[u32]) -> (BTreeMap<u64, u32>, u64) {
    program_at(instrs, 0x1000)
}
pub fn program_at(instrs: &[u32], base: u64) -> (BTreeMap<u64, u32>, u64) {
    (
        instrs
            .iter()
            .enumerate()
            .map(|(k, &w)| (base + 4 * k as u64, w))
            .collect(),
        base,
    )
}

/// Load a 32-bit signed constant using lui+addiw (Python `li32`).
pub fn li32(rd: u32, v: u32) -> Vec<u32> {
    let lo = (((v & 0xFFF) ^ 0x800) as i64) - 0x800;
    let hi = ((i64::from(v) - lo) >> 12) as u32 & 0xFFFFF;
    vec![lui(rd, hi), addiw(rd, rd, lo)]
}

/// Python `HALT`: `a7 = 0; ecall`.
pub fn halt() -> Vec<u32> {
    vec![addi(17, 0, 0), ecall()]
}

/// `x{rd} = RAM_BASE` (lui sign-extends, so build it with slli).
pub fn prologue_ram_base(rd: u32) -> Vec<u32> {
    vec![addi(rd, 0, 1), slli(rd, rd, 31)]
}

/// Build the 64-bit value `v` in register 7 from halves, as the Python
/// shift tests do (uses x8 as scratch).
pub fn li64_x7(v: u64) -> Vec<u32> {
    let mut p = li32(7, (v >> 32) as u32);
    p.push(slli(7, 7, 32));
    p.extend(li32(8, v as u32));
    p.extend([slli(8, 8, 32), srli(8, 8, 32), or_(7, 7, 8)]);
    p
}

/// Store the 64-bit constant `data` at `0(x1)`, as the Python
/// load/store tests do (x1 = RAM_BASE must already hold).
pub fn store_const_x1(data: u64) -> Vec<u32> {
    let mut p = li32(2, (data >> 32) as u32);
    p.push(slli(2, 2, 32));
    p.extend(li32(3, data as u32));
    p.extend([slli(3, 3, 32), srli(3, 3, 32), or_(2, 2, 3), sd(2, 1, 0)]);
    p
}

/// Deterministic xorshift64* RNG for the randomized tests (no `rand` dep).
pub struct Rng(pub u64);
impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    pub fn choice<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}
