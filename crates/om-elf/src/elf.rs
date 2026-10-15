//! Minimal ELF64 loader for guest programs (spec section 14.2).
//!
//! Mirrors `reference/openmagnetar/elf.py`: the header and program headers
//! are parsed manually (no ELF crate), checks run in Python's order, and
//! any failed check rejects the whole file.

use std::collections::BTreeMap;
use std::fmt;

use crate::abi::{AbiError, Params, RAM_BASE, memory_map};

/// `EM_RISCV`.
pub const EM_RISCV: u16 = 243;
/// `ET_EXEC`.
pub const ET_EXEC: u16 = 2;
/// `PT_LOAD`.
pub const PT_LOAD: u32 = 1;
/// `PT_NULL`.
pub const PT_NULL: u32 = 0;
/// `PT_NOTE`.
pub const PT_NOTE: u32 = 4;
/// `PT_PHDR`.
pub const PT_PHDR: u32 = 6;
/// `PT_TLS`.
pub const PT_TLS: u32 = 7;
/// `PT_GNU_STACK`.
pub const PT_GNU_STACK: u32 = 0x6474_e551;
/// `PT_RISCV_ATTRIBUTES`.
pub const PT_RISCV_ATTRIBUTES: u32 = 0x7000_0003;
/// `PF_X` (executable).
pub const PF_X: u32 = 1;
/// `PF_W` (writable).
pub const PF_W: u32 = 2;
/// `PF_R` (readable).
pub const PF_R: u32 = 4;
/// `EF_RISCV_RVC` (bit 0).
pub const EF_RISCV_RVC: u32 = 1;
/// `EF_RISCV_FLOAT_ABI` mask (bits 1–2).
pub const EF_RISCV_FLOAT_ABI: u32 = 6;
/// `EF_RISCV_RVE` (bit 3).
pub const EF_RISCV_RVE: u32 = 8;
/// `EF_RISCV_TSO` (bit 4).
pub const EF_RISCV_TSO: u32 = 0x10;
/// Program-header types ignored by the loader (14.2 step 2).
pub const IGNORED_PT: [u32; 5] = [PT_NULL, PT_NOTE, PT_PHDR, PT_GNU_STACK, PT_RISCV_ATTRIBUTES];

/// A rejected ELF file (Python `ElfError`, a subclass of `AbiError`).
/// The `Display` strings reproduce the Python messages exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElfError {
    /// Invalid ABI parameters (`Params::validate`).
    Abi(AbiError),
    /// Shorter than 64 bytes, or bad magic.
    NotElf,
    /// `EI_CLASS != 2` or `EI_DATA != 1`.
    NotElf64LittleEndian,
    /// `e_type != ET_EXEC`.
    BadType,
    /// `e_machine != EM_RISCV`.
    BadMachine,
    /// `e_flags` has the RVC bit.
    RvcFlag,
    /// `e_flags` has a float-ABI bit.
    FloatAbiFlag,
    /// `e_flags` has the RVE or TSO bit.
    RveTsoFlag,
    /// `e_phnum == 0` or `e_phentsize != 56`.
    BadProgramHeaderTable,
    /// The program-header table extends past the end of the file.
    ProgramHeadersOutOfFile,
    /// A non-`PT_LOAD` type that is not ignored.
    UnsupportedProgramHeaderType {
        /// The offending `p_type`.
        p_type: u32,
    },
    /// `p_filesz > p_memsz`.
    FileszExceedsMemsz,
    /// The segment's file bytes extend past the end of the file.
    SegmentOutOfFile,
    /// A segment that is both executable and writable.
    ExecutableWritableSegment,
    /// Code segment not 4-aligned, not a multiple of 4, or
    /// `p_filesz != p_memsz`.
    BadCodeSegmentShape,
    /// Code segment at or above `2^32`, or intersecting RAM.
    CodeSegmentOutOfRange,
    /// Two code segments overlap.
    OverlappingCodeSegments,
    /// An instruction word with `w % 4 != 3`.
    Non32BitInstruction {
        /// Byte address of the offending word.
        addr: u64,
    },
    /// Data segment outside `[RAM_BASE, RAM_BASE + 8 * in_base)`.
    DataSegmentOutOfRange,
    /// Two data segments overlap.
    OverlappingDataSegments,
    /// No executable segment.
    NoExecutableSegment,
    /// More than `max_code_words` instructions.
    CodeTooLarge,
    /// `e_entry` is not 4-aligned or is not an instruction address.
    BadEntryPoint,
}

impl From<AbiError> for ElfError {
    fn from(e: AbiError) -> Self {
        ElfError::Abi(e)
    }
}

impl fmt::Display for ElfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ElfError::Abi(e) => e.fmt(f),
            ElfError::NotElf => f.write_str("not an ELF file"),
            ElfError::NotElf64LittleEndian => f.write_str("must be ELF64 little-endian"),
            ElfError::BadType => f.write_str("e_type must be ET_EXEC"),
            ElfError::BadMachine => f.write_str("e_machine must be EM_RISCV"),
            ElfError::RvcFlag => f.write_str("RVC (compressed) is not allowed"),
            ElfError::FloatAbiFlag => f.write_str("floating-point ABI is not allowed"),
            ElfError::RveTsoFlag => f.write_str("RVE/TSO flags are not allowed"),
            ElfError::BadProgramHeaderTable => f.write_str("bad program header table"),
            ElfError::ProgramHeadersOutOfFile => f.write_str("program headers out of file"),
            ElfError::UnsupportedProgramHeaderType { p_type } => {
                write!(f, "unsupported program header type {p_type:#x}")
            }
            ElfError::FileszExceedsMemsz => f.write_str("p_filesz > p_memsz"),
            ElfError::SegmentOutOfFile => f.write_str("segment data out of file"),
            ElfError::ExecutableWritableSegment => f.write_str("executable+writable segment"),
            ElfError::BadCodeSegmentShape => {
                f.write_str("code segment must be 4-aligned, filesz == memsz, multiple of 4")
            }
            ElfError::CodeSegmentOutOfRange => {
                f.write_str("code segment must lie below 2^32 and outside RAM")
            }
            ElfError::OverlappingCodeSegments => f.write_str("overlapping code segments"),
            ElfError::Non32BitInstruction { addr } => {
                write!(f, "non-32-bit instruction encoding at {addr:#x}")
            }
            ElfError::DataSegmentOutOfRange => {
                f.write_str("data segment outside RAM or inside the I/O/stack area")
            }
            ElfError::OverlappingDataSegments => f.write_str("overlapping data segments"),
            ElfError::NoExecutableSegment => f.write_str("no executable segment"),
            ElfError::CodeTooLarge => f.write_str("code too large"),
            ElfError::BadEntryPoint => f.write_str("entry point not at an instruction"),
        }
    }
}

impl std::error::Error for ElfError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ElfError::Abi(e) => Some(e),
            _ => None,
        }
    }
}

/// A loaded guest program (Python's `(code, entry_pc, ram_words)` tuple).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedImage {
    /// Instruction words by pc (byte address → `u32`), for the bytecode ROM.
    pub code: BTreeMap<u64, u32>,
    /// `e_entry`, a key of `code`.
    pub entry_pc: u64,
    /// The program part of `M_0`: RAM word index → word, non-zero only.
    pub ram_words: BTreeMap<usize, u64>,
}

fn u16le(elf: &[u8], off: usize) -> u16 {
    u16::from_le_bytes(elf[off..off + 2].try_into().expect("2 bytes"))
}

fn u32le(elf: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(elf[off..off + 4].try_into().expect("4 bytes"))
}

fn u64le(elf: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(elf[off..off + 8].try_into().expect("8 bytes"))
}

/// Load an ELF64 little-endian RISC-V executable per 14.2: code segments
/// become the `code` map (never RAM; Harvard, C5), data segments are
/// packed into RAM words below the I/O window. Any failed check rejects
/// the file with no partial result.
pub fn load(elf: &[u8], params: &Params) -> Result<LoadedImage, ElfError> {
    params.validate()?;
    let mm = memory_map(params)?;
    if elf.len() < 64 || &elf[..4] != b"\x7fELF" {
        return Err(ElfError::NotElf);
    }
    if elf[4] != 2 || elf[5] != 1 {
        return Err(ElfError::NotElf64LittleEndian);
    }
    let e_type = u16le(elf, 16);
    let e_machine = u16le(elf, 18);
    let e_entry = u64le(elf, 24);
    let e_phoff = u64le(elf, 32);
    let e_flags = u32le(elf, 48);
    let e_phentsize = u16le(elf, 54);
    let e_phnum = u16le(elf, 56);
    if e_type != ET_EXEC {
        return Err(ElfError::BadType);
    }
    if e_machine != EM_RISCV {
        return Err(ElfError::BadMachine);
    }
    if e_flags & EF_RISCV_RVC != 0 {
        return Err(ElfError::RvcFlag);
    }
    if e_flags & EF_RISCV_FLOAT_ABI != 0 {
        return Err(ElfError::FloatAbiFlag);
    }
    if e_flags & (EF_RISCV_RVE | EF_RISCV_TSO) != 0 {
        return Err(ElfError::RveTsoFlag);
    }
    if e_phnum == 0 || e_phentsize != 56 {
        return Err(ElfError::BadProgramHeaderTable);
    }
    // Python compares in unbounded integers; overflow means "out of file".
    let ph_end = e_phoff
        .checked_add(u64::from(e_phnum) * 56)
        .filter(|&end| end <= elf.len() as u64)
        .ok_or(ElfError::ProgramHeadersOutOfFile)?;

    let ram_end = RAM_BASE + 8 * mm.ram_words as u64;
    let data_limit = RAM_BASE + 8 * mm.io_window_base as u64;
    let mut code: BTreeMap<u64, u32> = BTreeMap::new();
    let mut code_ranges: Vec<(u64, u64)> = Vec::new();
    let mut data_ranges: Vec<(u64, u64)> = Vec::new();
    let mut ram_bytes: BTreeMap<u64, u8> = BTreeMap::new(); // byte addr -> non-zero byte

    for i in 0..u64::from(e_phnum) {
        let off = (e_phoff + 56 * i) as usize;
        debug_assert!(off + 56 <= ph_end as usize);
        let p_type = u32le(elf, off);
        let p_flags = u32le(elf, off + 4);
        let p_offset = u64le(elf, off + 8);
        let p_vaddr = u64le(elf, off + 16);
        let p_filesz = u64le(elf, off + 32);
        let p_memsz = u64le(elf, off + 40);
        if p_type != PT_LOAD {
            if IGNORED_PT.contains(&p_type) {
                continue;
            }
            return Err(ElfError::UnsupportedProgramHeaderType { p_type });
        }
        if p_memsz == 0 {
            continue;
        }
        if p_filesz > p_memsz {
            return Err(ElfError::FileszExceedsMemsz);
        }
        let seg_end = p_offset
            .checked_add(p_filesz)
            .filter(|&end| end <= elf.len() as u64)
            .ok_or(ElfError::SegmentOutOfFile)?;
        if p_flags & PF_X != 0 && p_flags & PF_W != 0 {
            return Err(ElfError::ExecutableWritableSegment);
        }
        let lo = p_vaddr;
        let seg = &elf[p_offset as usize..seg_end as usize];
        if p_flags & PF_X != 0 {
            if !lo.is_multiple_of(4) || !p_memsz.is_multiple_of(4) || p_filesz != p_memsz {
                return Err(ElfError::BadCodeSegmentShape);
            }
            // An overflowing `lo + p_memsz` is above 2^32 in Python too.
            let hi = lo
                .checked_add(p_memsz)
                .ok_or(ElfError::CodeSegmentOutOfRange)?;
            if hi > 1 << 32 || (lo < ram_end && hi > RAM_BASE) {
                return Err(ElfError::CodeSegmentOutOfRange);
            }
            if code_ranges.iter().any(|&(a, b)| lo < b && a < hi) {
                return Err(ElfError::OverlappingCodeSegments);
            }
            code_ranges.push((lo, hi));
            for (k, chunk) in seg.as_chunks::<4>().0.iter().enumerate() {
                let w = u32::from_le_bytes(*chunk);
                let addr = lo + 4 * k as u64;
                if w & 3 != 3 {
                    return Err(ElfError::Non32BitInstruction { addr });
                }
                code.insert(addr, w);
            }
        } else {
            let hi = lo
                .checked_add(p_memsz)
                .ok_or(ElfError::DataSegmentOutOfRange)?;
            if lo < RAM_BASE || hi > data_limit {
                return Err(ElfError::DataSegmentOutOfRange);
            }
            if data_ranges.iter().any(|&(a, b)| lo < b && a < hi) {
                return Err(ElfError::OverlappingDataSegments);
            }
            data_ranges.push((lo, hi));
            for (j, &byte) in seg.iter().enumerate() {
                if byte != 0 {
                    ram_bytes.insert(lo + j as u64, byte);
                }
            }
        }
    }

    if code.is_empty() {
        return Err(ElfError::NoExecutableSegment);
    }
    if code.len() as u64 > params.max_code_words {
        return Err(ElfError::CodeTooLarge);
    }
    if !e_entry.is_multiple_of(4) || !code.contains_key(&e_entry) {
        return Err(ElfError::BadEntryPoint);
    }

    let mut ram_words: BTreeMap<usize, u64> = BTreeMap::new();
    for (addr, byte) in ram_bytes {
        let w = ((addr - RAM_BASE) >> 3) as usize;
        *ram_words.entry(w).or_insert(0) |= u64::from(byte) << (8 * (addr & 7));
    }
    Ok(LoadedImage {
        code,
        entry_pc: e_entry,
        ram_words,
    })
}
