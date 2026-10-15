"""Tiny RV64I assembler for tests (no toolchain available)."""

M32 = 0xFFFFFFFF


def _r(f7, rs2, rs1, f3, rd, opc):
    return ((f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opc) & M32


def _i(imm, rs1, f3, rd, opc):
    return (((imm & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | opc) & M32


def _s(imm, rs2, rs1, f3, opc=0x23):
    imm &= 0xFFF
    return (((imm >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((imm & 31) << 7) | opc) & M32


def _b(imm, rs2, rs1, f3):
    imm &= 0x1FFF
    return ((((imm >> 12) & 1) << 31) | (((imm >> 5) & 0x3F) << 25) | (rs2 << 20) | (rs1 << 15)
            | (f3 << 12) | (((imm >> 1) & 0xF) << 8) | (((imm >> 11) & 1) << 7) | 0x63) & M32


def _u(imm20, rd, opc):
    return (((imm20 & 0xFFFFF) << 12) | (rd << 7) | opc) & M32


def _j(imm, rd):
    imm &= 0x1FFFFF
    return ((((imm >> 20) & 1) << 31) | (((imm >> 1) & 0x3FF) << 21) | (((imm >> 11) & 1) << 20)
            | (((imm >> 12) & 0xFF) << 12) | (rd << 7) | 0x6F) & M32


OPI = dict(addi=0, slti=2, sltiu=3, xori=4, ori=6, andi=7)
OPR = dict(add=(0, 0), sub=(0x20, 0), sll=(0, 1), slt=(0, 2), sltu=(0, 3), xor=(0, 4),
           srl=(0, 5), sra=(0x20, 5), or_=(0, 6), and_=(0, 7))
OPW = dict(addw=(0, 0), subw=(0x20, 0), sllw=(0, 1), srlw=(0, 5), sraw=(0x20, 5))
BR = dict(beq=0, bne=1, blt=4, bge=5, bltu=6, bgeu=7)
LD = dict(lb=0, lh=1, lw=2, ld=3, lbu=4, lhu=5, lwu=6)
ST = dict(sb=0, sh=1, sw=2, sd=3)


def asm(op, *a):
    if op in OPI:
        rd, rs1, imm = a
        return _i(imm, rs1, OPI[op], rd, 0x13)
    if op in OPR:
        rd, rs1, rs2 = a
        f7, f3 = OPR[op]
        return _r(f7, rs2, rs1, f3, rd, 0x33)
    if op in OPW:
        rd, rs1, rs2 = a
        f7, f3 = OPW[op]
        return _r(f7, rs2, rs1, f3, rd, 0x3B)
    if op in ("slli", "srli", "srai"):
        rd, rs1, sh = a
        f3, f6 = {"slli": (1, 0), "srli": (5, 0), "srai": (5, 0x10)}[op]
        return _i((f6 << 6) | sh, rs1, f3, rd, 0x13)
    if op == "addiw":
        rd, rs1, imm = a
        return _i(imm, rs1, 0, rd, 0x1B)
    if op in ("slliw", "srliw", "sraiw"):
        rd, rs1, sh = a
        f3, f7 = {"slliw": (1, 0), "srliw": (5, 0), "sraiw": (5, 0x20)}[op]
        return _i((f7 << 5) | sh, rs1, f3, rd, 0x1B)
    if op in BR:
        rs1, rs2, off = a
        return _b(off, rs2, rs1, BR[op])
    if op in LD:
        rd, rs1, imm = a
        return _i(imm, rs1, LD[op], rd, 0x03)
    if op in ST:
        rs2, rs1, imm = a
        return _s(imm, rs2, rs1, ST[op])
    if op == "lui":
        return _u(a[1], a[0], 0x37)
    if op == "auipc":
        return _u(a[1], a[0], 0x17)
    if op == "jal":
        return _j(a[1], a[0])
    if op == "jalr":
        rd, rs1, imm = a
        return _i(imm, rs1, 0, rd, 0x67)
    if op == "fence":
        return 0x0FF0000F
    if op == "ecall":
        return 0x73
    if op == "ebreak":
        return 0x00100073
    raise ValueError(op)


def program(instrs, base=0x1000):
    """instrs: list of (op, *args) tuples -> (code dict, entry_pc)."""
    return {base + 4 * k: asm(*ins) for k, ins in enumerate(instrs)}, base


def li32(rd, v):
    """Load a 32-bit signed constant using lui+addiw."""
    v &= M32
    lo = ((v & 0xFFF) ^ 0x800) - 0x800
    hi = ((v - lo) >> 12) & 0xFFFFF
    return [("lui", rd, hi), ("addiw", rd, rd, lo)]


HALT = [("addi", 17, 0, 0), ("ecall",)]
