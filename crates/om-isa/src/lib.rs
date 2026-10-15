//! Strict RV64I and the virtual instruction set for Open Magnetar.
//!
//! Normative reference: `docs/spec/09-isa.md` (with CONVENTIONS C5, C6,
//! C7). Behavioral reference: `reference/openmagnetar/riscv.py`, mirrored
//! in [`riscv`] (decoder, plain interpreter — the oracle), and
//! `reference/openmagnetar/bytecode.py`, mirrored in [`bytecode`] (ROM
//! columns, `expand`, `datapath`, `VirtualMachine`). This crate has no
//! `om-*` dependencies: the Python modules it mirrors import nothing
//! beyond each other, and the field-valued Shout bytecode table of spec
//! 11 is built on top of [`bytecode::Row::get`] /
//! [`bytecode::Row::values`].
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python's stringly-typed `Instr.name` is the enum [`riscv::Op`];
//!   `Op::name()` returns the exact Python mnemonic. `LOAD_INFO` /
//!   `STORE_INFO` are `Op::load_info()` / `Op::store_info()`.
//! - Python `Trap("…")` is the typed error [`riscv::Trap`], returned as
//!   `Err` from every `step`/`run`; its `Display` strings reproduce the
//!   Python messages. Unprovable conditions are exactly Python's.
//! - Python `assert`/`ValueError` programmer errors (bad shift kind, a
//!   non-one-hot selector, `entry_pc` not in code, a non-ALU op passed
//!   to `alu`, a nonzero x0 write) panic, matching the other `om-*`
//!   crates.
//! - Code images and RAM are `BTreeMap`s (Python dicts); RAM maps word
//!   index → word and holds no zero words, as in Python. Registers are
//!   fixed arrays (`[u64; 32]` plain, `[u64; 64]` virtual).
//! - Python's row dicts are [`bytecode::Row`] structs with the flag
//!   columns as `bool` fields; `Q_lo`/`Q_hi` are `q_lo`/`q_hi`.
//!   `Row::get("Q_lo")` keeps Python's column-name access, and
//!   `Row::values()` gives all columns in `COLUMNS` order.
//! - Python's `datapath`/trace dicts are [`bytecode::Datapath`] and
//!   [`bytecode::TraceRecord`]; see their docs for the field-name map.
//!   One-bit Python ints become `bool` where they are pure flags.
//! - Spec 9.1's one deviation is kept: a load into `x0` expands to a
//!   NOP, so the virtual machine does not trap on it where the plain
//!   [`riscv::Machine`] does.

pub mod bytecode;
pub mod riscv;

pub use bytecode::{
    COLUMNS, Column, Datapath, FLAG_NAMES, HALTED_UPC, Program, Row, TEMP_REG, TRAP_UPC,
    TraceRecord, VMResult, VirtualMachine, bit, blank_row, column_by_name, datapath, expand,
    expand_instr, kind, kind_of, lane_mask, onehot_index, run_program, shift_apply, store_apply,
};
pub use riscv::{
    ExecResult, Instr, M32, M64, Machine, Op, RAM_BASE, Trap, alu, decode, s64, sext, sext32,
};
