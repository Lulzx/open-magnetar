"""Minimal ELF64 loader for guest programs (spec section 14.2)."""
from __future__ import annotations

import struct

from .abi import RAM_BASE, AbiError, Params, memory_map

EM_RISCV = 243
ET_EXEC = 2
PT_LOAD, PT_NULL, PT_NOTE, PT_PHDR, PT_TLS = 1, 0, 4, 6, 7
PT_GNU_STACK = 0x6474E551
PT_RISCV_ATTRIBUTES = 0x70000003
PF_X, PF_W, PF_R = 1, 2, 4
EF_RISCV_RVC, EF_RISCV_FLOAT_ABI, EF_RISCV_RVE, EF_RISCV_TSO = 1, 6, 8, 0x10
IGNORED_PT = {PT_NULL, PT_NOTE, PT_PHDR, PT_GNU_STACK, PT_RISCV_ATTRIBUTES}


class ElfError(AbiError):
    pass


def load(elf: bytes, params: Params):
    """Return (code: dict pc->u32, entry_pc: int, ram_words: dict word->u64).

    ram_words holds only non-zero words. Raises ElfError on any violation.
    """
    params.validate()
    mm = memory_map(params)
    if len(elf) < 64 or elf[:4] != b"\x7fELF":
        raise ElfError("not an ELF file")
    if elf[4] != 2 or elf[5] != 1:
        raise ElfError("must be ELF64 little-endian")
    (e_type, e_machine, _ver, e_entry, e_phoff, _shoff, e_flags, _ehsize,
     e_phentsize, e_phnum) = struct.unpack_from("<HHIQQQIHHH", elf, 16)
    if e_type != ET_EXEC:
        raise ElfError("e_type must be ET_EXEC")
    if e_machine != EM_RISCV:
        raise ElfError("e_machine must be EM_RISCV")
    if e_flags & EF_RISCV_RVC:
        raise ElfError("RVC (compressed) is not allowed")
    if e_flags & EF_RISCV_FLOAT_ABI:
        raise ElfError("floating-point ABI is not allowed")
    if e_flags & (EF_RISCV_RVE | EF_RISCV_TSO):
        raise ElfError("RVE/TSO flags are not allowed")
    if e_phnum == 0 or e_phentsize != 56:
        raise ElfError("bad program header table")
    if e_phoff + e_phnum * 56 > len(elf):
        raise ElfError("program headers out of file")

    ram_end = RAM_BASE + 8 * mm.ram_words
    data_limit = RAM_BASE + 8 * mm.io_window_base
    code: dict[int, int] = {}
    code_ranges: list[tuple[int, int]] = []
    data_ranges: list[tuple[int, int]] = []
    ram_bytes: dict[int, int] = {}  # byte addr -> non-zero byte value

    for i in range(e_phnum):
        (p_type, p_flags, p_offset, p_vaddr, _paddr, p_filesz, p_memsz,
         p_align) = struct.unpack_from("<IIQQQQQQ", elf, e_phoff + 56 * i)
        if p_type != PT_LOAD:
            if p_type in IGNORED_PT:
                continue
            raise ElfError(f"unsupported program header type {p_type:#x}")
        if p_memsz == 0:
            continue
        if p_filesz > p_memsz:
            raise ElfError("p_filesz > p_memsz")
        if p_offset + p_filesz > len(elf):
            raise ElfError("segment data out of file")
        if (p_flags & PF_X) and (p_flags & PF_W):
            raise ElfError("executable+writable segment")
        lo, hi = p_vaddr, p_vaddr + p_memsz
        seg = elf[p_offset:p_offset + p_filesz]
        if p_flags & PF_X:
            if lo % 4 or p_memsz % 4 or p_filesz != p_memsz:
                raise ElfError("code segment must be 4-aligned, filesz == memsz, multiple of 4")
            if lo < 0 or hi > 1 << 32 or (lo < ram_end and hi > RAM_BASE):
                raise ElfError("code segment must lie below 2^32 and outside RAM")
            for a, b in code_ranges:
                if lo < b and a < hi:
                    raise ElfError("overlapping code segments")
            code_ranges.append((lo, hi))
            for off in range(0, p_memsz, 4):
                w = int.from_bytes(seg[off:off + 4], "little")
                if w & 3 != 3:
                    raise ElfError(f"non-32-bit instruction encoding at {lo + off:#x}")
                code[lo + off] = w
        else:
            if lo < RAM_BASE or hi > data_limit:
                raise ElfError("data segment outside RAM or inside the I/O/stack area")
            for a, b in data_ranges:
                if lo < b and a < hi:
                    raise ElfError("overlapping data segments")
            data_ranges.append((lo, hi))
            for off, byte in enumerate(seg):
                if byte:
                    ram_bytes[lo + off] = byte

    if not code:
        raise ElfError("no executable segment")
    if len(code) > params.max_code_words:
        raise ElfError("code too large")
    if e_entry % 4 or e_entry not in code:
        raise ElfError("entry point not at an instruction")

    ram_words: dict[int, int] = {}
    for addr, byte in ram_bytes.items():
        w = (addr - RAM_BASE) >> 3
        ram_words[w] = ram_words.get(w, 0) | (byte << (8 * (addr & 7)))
    return code, e_entry, ram_words
