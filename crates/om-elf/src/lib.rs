//! Guest ABI and ELF64 loader for Open Magnetar.
//!
//! Normative reference: `docs/spec/14-guest-abi.md` (with CONVENTIONS C5
//! and C6). Behavioral reference: `reference/openmagnetar/abi.py`,
//! mirrored in [`abi`] (memory map, I/O region encoding, `M_0`
//! construction, program digest, public instance), and
//! `reference/openmagnetar/elf.py`, mirrored in [`elf`] ([`load`] parses
//! ELF64 manually; no ELF crate). The loaded image feeds
//! `om_isa::Machine` / the bytecode ROM after [`build_m0`].
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python `AbiError` is the typed enum [`AbiError`] and `ElfError` the
//!   typed enum [`ElfError`] (with an `Abi` variant for the Python
//!   subclass relationship); both are returned as `Err`. Their `Display`
//!   strings reproduce the Python messages exactly. Non-`AbiError`
//!   Python failures (`bytes([A, I, O])` overflow, `IndexError` on a
//!   short dense RAM) panic, matching the other `om-*` crates.
//! - `Params.hash_profile` is the typed [`Hasher`] instead of a string.
//!   [`program_digest`] keeps Python's hash choice exactly: SHA3-256 iff
//!   the profile is `sha3-256`, SHA-256 otherwise.
//! - Code images and RAM are `BTreeMap`s (Python dicts), as in `om-isa`:
//!   code maps pc → `u32`, RAM maps word index → `u64`, non-zero only
//!   where Python keeps it sparse.
//! - Python's `load` tuple is the struct [`LoadedImage`]; Python's
//!   dict-or-list `final_ram` argument splits into
//!   [`output_region_words`]/[`extract_output`] (sparse) and
//!   [`output_region_words_slice`]/[`extract_output_slice`] (dense).
//! - Python's bit lists (`list[int]` of 0/1) are `Vec<bool>`, matching
//!   `om_sumcheck::mle_eval_bits`.

pub mod abi;
pub mod elf;

pub use abi::{
    AbiError, CODE_BASE, DIGEST_DOMAIN, MASK64, MemoryMap, Params, PublicInstance, RAM_BASE,
    build_m0, decode_region, encode_region, expected_output_mle_eval, extract_output,
    extract_output_slice, input_words, memory_map, output_region_bits, output_region_words,
    output_region_words_slice, program_digest,
};
pub use elf::{
    EF_RISCV_FLOAT_ABI, EF_RISCV_RVC, EF_RISCV_RVE, EF_RISCV_TSO, EM_RISCV, ET_EXEC, ElfError,
    IGNORED_PT, LoadedImage, PF_R, PF_W, PF_X, PT_GNU_STACK, PT_LOAD, PT_NOTE, PT_NULL, PT_PHDR,
    PT_RISCV_ATTRIBUTES, PT_TLS, load,
};
pub use om_transcript::Hasher;
