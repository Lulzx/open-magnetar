"""RV64I decoder and plain reference interpreter (the oracle).

Semantics follow The RISC-V Instruction Set Manual, Volume I: Unprivileged
ISA (RV64I base, chapters 2 and 5). Machine model per CONVENTIONS C5/C6.
Conditions that C5/C6 declare "unprovable" raise `Trap`.
"""

from __future__ import annotations

from dataclasses import dataclass, field

M64 = (1 << 64) - 1
M32 = (1 << 32) - 1
RAM_BASE = 0x8000_0000


class Trap(Exception):
    """An unprovable condition (misaligned/out-of-range access, bad ECALL, EBREAK, illegal)."""


def sext(x: int, bits: int) -> int:
    x &= (1 << bits) - 1
    return x - (1 << bits) if x >> (bits - 1) else x


def u64(x: int) -> int:
    return x & M64


def s64(x: int) -> int:
    return sext(x, 64)


@dataclass(frozen=True)
class Instr:
    name: str          # mnemonic in upper case, or "ILLEGAL"
    rd: int = 0
    rs1: int = 0
    rs2: int = 0
    imm: int = 0       # signed immediate (shamt for shifts; U-type: imm20 << 12 sign-extended)
    word: int = 0


_BRANCH = {0: "BEQ", 1: "BNE", 4: "BLT", 5: "BGE", 6: "BLTU", 7: "BGEU"}
_LOAD = {0: "LB", 1: "LH", 2: "LW", 3: "LD", 4: "LBU", 5: "LHU", 6: "LWU"}
_STORE = {0: "SB", 1: "SH", 2: "SW", 3: "SD"}
_OPIMM = {0: "ADDI", 2: "SLTI", 3: "SLTIU", 4: "XORI", 6: "ORI", 7: "ANDI"}
_OP = {(0, 0): "ADD", (0x20, 0): "SUB", (0, 1): "SLL", (0, 2): "SLT", (0, 3): "SLTU",
       (0, 4): "XOR", (0, 5): "SRL", (0x20, 5): "SRA", (0, 6): "OR", (0, 7): "AND"}
_OP32 = {(0, 0): "ADDW", (0x20, 0): "SUBW", (0, 1): "SLLW", (0, 5): "SRLW", (0x20, 5): "SRAW"}


def decode(word: int) -> Instr:
    w = word & M32
    bad = Instr("ILLEGAL", word=w)
    opc = w & 0x7F
    rd = (w >> 7) & 31
    f3 = (w >> 12) & 7
    rs1 = (w >> 15) & 31
    rs2 = (w >> 20) & 31
    f7 = (w >> 25) & 0x7F
    imm_i = sext(w >> 20, 12)
    imm_s = sext(((w >> 25) << 5) | ((w >> 7) & 31), 12)
    imm_b = sext(((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3F) << 5)
                 | (((w >> 8) & 0xF) << 1), 13)
    imm_u = sext(w & 0xFFFFF000, 32)
    imm_j = sext(((w >> 31) << 20) | (((w >> 12) & 0xFF) << 12) | (((w >> 20) & 1) << 11)
                 | (((w >> 21) & 0x3FF) << 1), 21)
    if opc == 0x37:
        return Instr("LUI", rd=rd, imm=imm_u, word=w)
    if opc == 0x17:
        return Instr("AUIPC", rd=rd, imm=imm_u, word=w)
    if opc == 0x6F:
        return Instr("JAL", rd=rd, imm=imm_j, word=w)
    if opc == 0x67:
        return Instr("JALR", rd=rd, rs1=rs1, imm=imm_i, word=w) if f3 == 0 else bad
    if opc == 0x63:
        return Instr(_BRANCH[f3], rs1=rs1, rs2=rs2, imm=imm_b, word=w) if f3 in _BRANCH else bad
    if opc == 0x03:
        return Instr(_LOAD[f3], rd=rd, rs1=rs1, imm=imm_i, word=w) if f3 in _LOAD else bad
    if opc == 0x23:
        return Instr(_STORE[f3], rs1=rs1, rs2=rs2, imm=imm_s, word=w) if f3 in _STORE else bad
    if opc == 0x13:
        if f3 in _OPIMM:
            return Instr(_OPIMM[f3], rd=rd, rs1=rs1, imm=imm_i, word=w)
        shamt = (w >> 20) & 0x3F
        f6 = w >> 26
        if f3 == 1 and f6 == 0:
            return Instr("SLLI", rd=rd, rs1=rs1, imm=shamt, word=w)
        if f3 == 5 and f6 == 0:
            return Instr("SRLI", rd=rd, rs1=rs1, imm=shamt, word=w)
        if f3 == 5 and f6 == 0x10:
            return Instr("SRAI", rd=rd, rs1=rs1, imm=shamt, word=w)
        return bad
    if opc == 0x1B:
        if f3 == 0:
            return Instr("ADDIW", rd=rd, rs1=rs1, imm=imm_i, word=w)
        if f3 == 1 and f7 == 0:
            return Instr("SLLIW", rd=rd, rs1=rs1, imm=rs2, word=w)
        if f3 == 5 and f7 == 0:
            return Instr("SRLIW", rd=rd, rs1=rs1, imm=rs2, word=w)
        if f3 == 5 and f7 == 0x20:
            return Instr("SRAIW", rd=rd, rs1=rs1, imm=rs2, word=w)
        return bad
    if opc == 0x33:
        n = _OP.get((f7, f3))
        return Instr(n, rd=rd, rs1=rs1, rs2=rs2, word=w) if n else bad
    if opc == 0x3B:
        n = _OP32.get((f7, f3))
        return Instr(n, rd=rd, rs1=rs1, rs2=rs2, word=w) if n else bad
    if opc == 0x0F:
        return Instr("FENCE", word=w) if f3 == 0 else bad     # FENCE.I (f3=1) is Zifencei: illegal
    if opc == 0x73:
        if w == 0x00000073:
            return Instr("ECALL", word=w)
        if w == 0x00100073:
            return Instr("EBREAK", word=w)
        return bad
    return bad


LOAD_INFO = {  # name -> (bytes, signed)
    "LB": (1, True), "LH": (2, True), "LW": (4, True), "LD": (8, False),
    "LBU": (1, False), "LHU": (2, False), "LWU": (4, False)}
STORE_INFO = {"SB": 1, "SH": 2, "SW": 4, "SD": 8}


def alu(name: str, a: int, b: int) -> int:
    """Register/immediate ALU operations on u64 inputs; returns u64."""
    sh = b & 63
    shw = b & 31
    if name in ("ADD", "ADDI"):
        return u64(a + b)
    if name == "SUB":
        return u64(a - b)
    if name in ("XOR", "XORI"):
        return a ^ b
    if name in ("OR", "ORI"):
        return a | b
    if name in ("AND", "ANDI"):
        return a & b
    if name in ("SLT", "SLTI"):
        return int(s64(a) < s64(b))
    if name in ("SLTU", "SLTIU"):
        return int(a < b)
    if name in ("SLL", "SLLI"):
        return u64(a << sh)
    if name in ("SRL", "SRLI"):
        return a >> sh
    if name in ("SRA", "SRAI"):
        return u64(s64(a) >> sh)
    if name in ("ADDW", "ADDIW"):
        return u64(sext(a + b, 32))
    if name == "SUBW":
        return u64(sext(a - b, 32))
    if name in ("SLLW", "SLLIW"):
        return u64(sext((a << shw) & M32, 32))
    if name in ("SRLW", "SRLIW"):
        return u64(sext((a & M32) >> shw, 32))
    if name in ("SRAW", "SRAIW"):
        return u64(sext(a & M32, 32) >> shw)
    raise ValueError(name)


@dataclass
class ExecResult:
    exit_code: int
    regs: list[int]
    ram: dict[int, int]
    instret: int


class Machine:
    """Plain RV64I interpreter over (code, entry_pc, ram_words)."""

    def __init__(self, code: dict[int, int], entry_pc: int, ram_words: dict[int, int],
                 ram_log_words: int):
        self.code = dict(code)
        self.pc = entry_pc
        self.ram = {k: v & M64 for k, v in ram_words.items() if v}
        self.A = ram_log_words
        self.regs = [0] * 32
        self.instret = 0

    # -- memory --------------------------------------------------------
    def _widx(self, addr: int, nbytes: int) -> tuple[int, int]:
        addr &= M64
        if addr & (nbytes - 1):
            raise Trap(f"misaligned access at {addr:#x}")
        off = addr - RAM_BASE
        if not (0 <= off < 8 << self.A):
            raise Trap(f"access out of range at {addr:#x}")
        return off >> 3, off & 7

    def load(self, addr: int, nbytes: int, signed: bool) -> int:
        idx, off = self._widx(addr, nbytes)
        v = (self.ram.get(idx, 0) >> (8 * off)) & ((1 << (8 * nbytes)) - 1)
        return u64(sext(v, 8 * nbytes)) if signed else v

    def store(self, addr: int, nbytes: int, val: int) -> None:
        idx, off = self._widx(addr, nbytes)
        mask = ((1 << (8 * nbytes)) - 1) << (8 * off)
        old = self.ram.get(idx, 0)
        new = (old & ~mask) | ((val << (8 * off)) & mask)
        if new:
            self.ram[idx] = new
        else:
            self.ram.pop(idx, None)

    def _wr(self, rd: int, v: int) -> None:
        if rd:
            self.regs[rd] = v & M64

    # -- execution -----------------------------------------------------
    def step(self) -> int | None:
        """Execute one instruction. Returns the exit code on HALT, else None."""
        pc = self.pc
        if pc not in self.code:
            raise Trap(f"fetch from {pc:#x}")
        i = decode(self.code[pc])
        n = i.name
        R = self.regs
        nxt = pc + 4
        if n == "ILLEGAL" or n == "EBREAK":
            raise Trap(f"{n} at {pc:#x}")
        if n == "LUI":
            self._wr(i.rd, u64(i.imm))
        elif n == "AUIPC":
            self._wr(i.rd, u64(pc + i.imm))
        elif n == "JAL":
            self._wr(i.rd, pc + 4)
            nxt = u64(pc + i.imm)
        elif n == "JALR":
            t = u64(R[i.rs1] + i.imm) & ~1
            self._wr(i.rd, pc + 4)
            nxt = t
        elif n in ("BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU"):
            a, b = R[i.rs1], R[i.rs2]
            t = {"BEQ": a == b, "BNE": a != b, "BLT": s64(a) < s64(b), "BGE": s64(a) >= s64(b),
                 "BLTU": a < b, "BGEU": a >= b}[n]
            if t:
                nxt = u64(pc + i.imm)
        elif n in LOAD_INFO:
            nb, sg = LOAD_INFO[n]
            self._wr(i.rd, self.load(R[i.rs1] + i.imm, nb, sg))
        elif n in STORE_INFO:
            self.store(R[i.rs1] + i.imm, STORE_INFO[n], R[i.rs2])
        elif n == "FENCE":
            pass
        elif n == "ECALL":
            if R[17] != 0:
                raise Trap("unsupported ECALL")
            self.instret += 1
            return R[10]
        else:
            imm_ops = n in _OPIMM.values() or n in ("SLLI", "SRLI", "SRAI", "ADDIW", "SLLIW", "SRLIW", "SRAIW")
            b = u64(i.imm) if imm_ops else R[i.rs2]
            self._wr(i.rd, alu(n, R[i.rs1], b))
        if nxt & 3:
            raise Trap("misaligned jump target")
        self.pc = nxt
        self.instret += 1
        return None

    def run(self, max_cycles: int) -> ExecResult:
        for _ in range(max_cycles):
            ec = self.step()
            if ec is not None:
                return ExecResult(ec, list(self.regs), dict(self.ram), self.instret)
        raise Trap("max_cycles exceeded")
