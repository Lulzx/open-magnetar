"""Virtual instruction set, RV64I -> bytecode-table expansion, and the virtual machine.

See docs/spec/09-isa.md. A *virtual instruction* is one ROM row; the circuit
(10-cpu-circuit.md) is a fixed datapath whose behaviour is steered entirely by
the row's columns. `datapath()` is the single source of truth for the
per-cycle intermediate values; `cpu_circuit.witness` copies them into W and
`cpu_circuit.check` verifies the R1CS relations independently.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .riscv import (M32, M64, Instr, LOAD_INFO, STORE_INFO, RAM_BASE, Trap, decode, sext, u64)

HALTED_UPC = 0
TRAP_UPC = 1
TEMP_REG = 32           # virtual register used by multi-cycle expansions
KIND = {"SLL": 0, "SRL": 1, "SRA": 2, "SLLW": 3, "SRLW": 4, "SRAW": 5, "SEXT32": 6, "ZEXT32": 7}


@dataclass(frozen=True)
class Column:
    name: str
    width: int
    meaning: str


def _flags():
    return [
        ("head", "first row of an RV64I instruction (valid JALR/branch target)"),
        ("halted", "HALTED padding row (binds exit code)"),
        ("ecall", "HALT row: requires a7 (rs2 value) = 0"),
        ("trap", "unprovable row: circuit requires trap = 0"),
        ("b_imm", "ALU B operand is imm (else rs2 value)"),
        ("sub", "adder subtracts (B inverted, carry-in 1)"),
        ("w", "sign-extend adder result from bit 31 (ADDW, SUBW, ADDIW, word shift stages)"),
        ("c_add", "result gets adder output S'"),
        ("e", "result gets XOR of operands (XOR, OR)"),
        ("g", "result gets AND of operands (AND, OR)"),
        ("f_ltu", "unsigned compare (SLTU, BLTU, BGEU)"),
        ("f_lts", "signed compare (SLT, BLT, BGE)"),
        ("f_cmp", "f_ltu or f_lts"),
        ("g_slt", "write comparison bit to rd (SLT, SLTU, SLTI, SLTIU)"),
        ("f_eq", "equality test (BEQ, BNE)"),
        ("br", "conditional branch"),
        ("inv", "invert branch condition"),
        ("sh_imm", "static (unconditional) shift"),
        ("mem", "RAM access (load or store)"),
        ("a_h", "access width >= 2 bytes (alignment)"),
        ("a_w", "access width >= 4 bytes"),
        ("a_d", "access width = 8 bytes"),
        ("jalr", "indirect jump: next micro-PC is dynamic"),
        ("ldsb", "signed byte load (sign = extracted bit 7)"),
        ("ldsh", "signed halfword load (bit 15)"),
        ("ldsw", "signed word load (bit 31)"),
    ]


FLAG_NAMES = [n for n, _ in _flags()]

COLUMNS: list[Column] = (
    [Column("upc", 32, "micro-PC of this row (identity column)"),
     Column("rpc", 64, "RV64I pc of the instruction this row belongs to"),
     Column("rs1", 6, "register read port 1 (6-bit index; virtual regs 32..63)"),
     Column("rs2", 6, "register read port 2"),
     Column("rd", 6, "register write port (0 = no write)"),
     Column("imm", 64, "sign-extended immediate (ALU B operand / address offset)"),
     Column("kc", 64, "constant result word (LUI, AUIPC, link address pc+4)"),
     Column("seq", 32, "next micro-PC when not taken / not indirect"),
     Column("tgt", 32, "next micro-PC when a branch is taken")]
    + [Column(n, 1, m) for n, m in _flags()]
    + [Column("bsel", 6, "one-hot: bit of rs2 value that conditions a shift stage (0 = unconditional)"),
       Column("ln", 8, "load: byte lanes copied from the extracted word"),
       Column("fill", 8, "load: byte lanes filled with the sign bit"),
       Column("st_w", 4, "store width one-hot {SB,SH,SW,SD} (router Q_st)"),
       Column("Q_lo", 64, "one-hot shift amount (router Q_lo); 0 if no shift"),
       Column("Q_hi", 8, "one-hot shift kind (router Q_hi); 0 if no shift")]
)
COLUMN_BY_NAME = {c.name: c for c in COLUMNS}


def blank_row() -> dict[str, int]:
    return {c.name: 0 for c in COLUMNS}


# ----------------------------------------------------------------------------
# Router semantics (C7), shared with the router agent
# ----------------------------------------------------------------------------

def shift_apply(kind: int, amt: int, src: int) -> int:
    src &= M64
    lo = src & M32
    if kind == 0:
        return u64(src << amt)
    if kind == 1:
        return src >> amt
    if kind == 2:
        return u64(sext(src, 64) >> amt)
    if kind == 3:
        return u64(sext((src << amt) & M32, 32)) if amt < 32 else 0
    if kind == 4:
        return u64(sext(lo >> amt, 32)) if amt < 32 else 0
    if kind == 5:
        return u64(sext(lo, 32) >> amt) if amt < 32 else 0
    if kind == 6:
        return u64(sext(lo, 32)) if amt == 0 else 0
    if kind == 7:
        return lo if amt == 0 else 0
    raise ValueError(kind)


def store_apply(width_sel: int, off: int, old: int, src: int) -> int:
    """New RAM word of a store. width_sel in 0..3 (SB,SH,SW,SD); off = low 3 address bits."""
    nb = 1 << width_sel
    mask = ((1 << (8 * nb)) - 1) << (8 * off)
    return (old & ~mask & M64) | ((src << (8 * off)) & mask)


def onehot_index(x: int) -> int | None:
    if x == 0:
        return None
    assert x & (x - 1) == 0, "not one-hot"
    return x.bit_length() - 1


def bit(x: int, i: int) -> int:
    return (x >> i) & 1


def lane_mask(lanes: int) -> int:
    return sum(0xFF << (8 * k) for k in range(8) if (lanes >> k) & 1)


# ----------------------------------------------------------------------------
# Per-cycle datapath (the semantics the circuit arithmetizes)
# ----------------------------------------------------------------------------

def datapath(row: dict[str, int], v1: int, v2: int, rw: int) -> dict[str, int]:
    r = row
    d: dict[str, int] = {}
    Bop = r["imm"] if r["b_imm"] else v2
    bp = Bop ^ (M64 if r["sub"] else 0)
    c = r["sub"]
    cin = 0
    for i in range(64):
        cin |= c << i
        a, b = bit(v1, i), bit(bp, i)
        c = (a & b) | (a & c) | (b & c)
    cout = c
    S = v1 ^ bp ^ cin
    s31 = bit(S, 31)
    Dw = ((S ^ (M64 if s31 else 0)) & (M32 << 32)) if r["w"] else 0
    Sp = S ^ Dw
    X = v1 ^ Bop
    AND = v1 & Bop
    T0 = Sp if r["c_add"] else 0
    T1 = T0 ^ (X if r["e"] else 0)
    T2 = T1 ^ (AND if r["g"] else 0)
    nw = 0
    n = bit(S, 0)
    for i in range(1, 64):
        n |= bit(S, i)
        nw |= n << i
    eq = 1 ^ n
    off = S & 7
    p = [bit(r["bsel"], k) & bit(v2, k) for k in range(6)]
    cond = r["sh_imm"]
    for pk in p:
        cond ^= pk
    qa, qk = onehot_index(r["Q_lo"]), onehot_index(r["Q_hi"])
    Y = shift_apply(qk, qa, v1) if (qa is not None and qk is not None) else 0
    Gs = (Sp ^ Y) if cond else 0
    ltu = 1 ^ cout
    u1 = r["f_cmp"] & ltu
    u2 = r["f_lts"] & (bit(v1, 63) ^ bit(Bop, 63))
    cmp_ = u1 ^ u2
    rdslt = r["g_slt"] & cmp_
    eqres = r["f_eq"] & eq
    take = r["br"] & (cmp_ ^ eqres ^ r["inv"])
    x1 = (rw >> 8) if bit(off, 0) else rw
    x2 = (x1 >> 16) if bit(off, 1) else x1
    x3 = (x2 >> 32) if bit(off, 2) else x2
    tb, th, tw = r["ldsb"] & bit(x3, 7), r["ldsh"] & bit(x3, 15), r["ldsw"] & bit(x3, 31)
    m = x3 & lane_mask(r["ln"])
    L = m ^ (lane_mask(r["fill"]) if (tb ^ th ^ tw) else 0)
    rdv = T2 ^ Gs ^ L ^ rdslt ^ r["kc"]
    d.update(Bop=Bop, cin=cin, cout=cout, S=S, Dw=Dw, Sp=Sp, X=X, AND=AND, T0=T0, T1=T1, T2=T2,
             nw=nw, eq=eq, off=off, p=p, cond=cond, Y=Y, Gs=Gs, u1=u1, u2=u2, cmp=cmp_,
             rdslt=rdslt, eqres=eqres, take=take, x1=x1, x2=x2, x3=x3, tb=tb, th=th, tw=tw,
             m=m, L=L, rdv=rdv, shift=(qk, qa) if Y is not None and qa is not None else None)
    return d


# ----------------------------------------------------------------------------
# Expansion
# ----------------------------------------------------------------------------

@dataclass
class Program:
    rom: list[dict[str, int]]
    columns: list[Column]
    upc_of_pc: dict[int, int]
    entry_pc: int
    entry_upc: int
    code: dict[int, int]
    cycles_of_pc: dict[int, int] = field(default_factory=dict)


_IMM_ALU = {"ADDI": "ADD", "SLTI": "SLT", "SLTIU": "SLTU", "XORI": "XOR", "ORI": "OR", "ANDI": "AND",
            "ADDIW": "ADDW"}
_RR_ALU = {"ADD", "SUB", "XOR", "OR", "AND", "SLT", "SLTU", "ADDW", "SUBW"}
_SHIFT_IMM = {"SLLI": "SLL", "SRLI": "SRL", "SRAI": "SRA", "SLLIW": "SLLW", "SRLIW": "SRLW", "SRAIW": "SRAW"}
_SHIFT_REG = {"SLL": "SLL", "SRL": "SRL", "SRA": "SRA", "SLLW": "SLLW", "SRLW": "SRLW", "SRAW": "SRAW"}


def _alu_flags(op: str) -> dict[str, int]:
    f = {"c_add": 0}
    if op in ("ADD", "ADDW"):
        f.update(c_add=1, w=int(op == "ADDW"))
    elif op in ("SUB", "SUBW"):
        f.update(c_add=1, sub=1, w=int(op == "SUBW"))
    elif op == "XOR":
        f.update(e=1)
    elif op == "OR":
        f.update(e=1, g=1)
    elif op == "AND":
        f.update(g=1)
    elif op == "SLT":
        f.update(sub=1, f_lts=1, f_cmp=1, g_slt=1)
    elif op == "SLTU":
        f.update(sub=1, f_ltu=1, f_cmp=1, g_slt=1)
    else:
        raise ValueError(op)
    return f


def _qsel(kind: str, amt: int) -> dict[str, int]:
    return {"Q_lo": 1 << amt, "Q_hi": 1 << KIND[kind]}


def expand_instr(i: Instr, pc: int, tgt_upc) -> list[dict[str, int]]:
    """Rows (without upc/rpc/seq filled, except explicit branch fields) for one instruction.

    `tgt_upc(pc)` returns the head micro-PC of an RV64I pc or TRAP_UPC.
    Returned rows carry the key '_seq' = 'next' (sequential) or an explicit upc.
    """
    n = i.name
    rows: list[dict[str, int]] = []

    def row(**kw):
        r = blank_row()
        r.update(kw)
        rows.append(r)
        return r

    if n in ("ILLEGAL", "EBREAK"):
        row(trap=1)
    elif n == "ECALL":
        row(ecall=1, rs1=10, rs2=17, seq=HALTED_UPC)
        rows[-1]["_seq"] = HALTED_UPC
    elif n == "FENCE":
        row()
    elif n in _IMM_ALU or n in _RR_ALU:
        if i.rd == 0:
            row()
        else:
            op = _IMM_ALU.get(n, n)
            f = _alu_flags(op)
            if n in _IMM_ALU:
                row(rs1=i.rs1, rd=i.rd, b_imm=1, imm=u64(i.imm), **f)
            else:
                row(rs1=i.rs1, rs2=i.rs2, rd=i.rd, **f)
    elif n in _SHIFT_IMM:
        if i.rd == 0:
            row()
        else:
            k = _SHIFT_IMM[n]
            row(rs1=i.rs1, rd=i.rd, b_imm=1, c_add=1, sh_imm=1, **_qsel(k, i.imm))
    elif n in _SHIFT_REG:
        if i.rd == 0:
            row()
        else:
            k = _SHIFT_REG[n]
            word = k.endswith("W")
            stages = range(5) if word else range(6)
            last = 4 if word else 5
            for s in stages:
                row(rs1=i.rs1 if s == 0 else TEMP_REG, rs2=i.rs2,
                    rd=i.rd if s == last else TEMP_REG, b_imm=1, c_add=1, w=int(word),
                    bsel=1 << s, **_qsel(k, 1 << s))
    elif n == "LUI":
        row(rd=i.rd, kc=u64(i.imm)) if i.rd else row()
    elif n == "AUIPC":
        row(rd=i.rd, kc=u64(pc + i.imm)) if i.rd else row()
    elif n == "JAL":
        row(rd=i.rd, kc=(pc + 4) if i.rd else 0)
        rows[-1]["_seq"] = tgt_upc(u64(pc + i.imm))
    elif n == "JALR":
        row(rs1=i.rs1, rd=i.rd, b_imm=1, imm=u64(i.imm), kc=(pc + 4) if i.rd else 0, jalr=1)
        rows[-1]["_seq"] = 0
    elif n in ("BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU"):
        f = dict(BEQ=dict(f_eq=1), BNE=dict(f_eq=1, inv=1), BLT=dict(f_lts=1, f_cmp=1),
                 BGE=dict(f_lts=1, f_cmp=1, inv=1), BLTU=dict(f_ltu=1, f_cmp=1),
                 BGEU=dict(f_ltu=1, f_cmp=1, inv=1))[n]
        row(rs1=i.rs1, rs2=i.rs2, sub=1, br=1, tgt=tgt_upc(u64(pc + i.imm)), **f)
    elif n in LOAD_INFO:
        nb, sg = LOAD_INFO[n]
        if i.rd == 0:
            row()
        else:
            ln = (1 << nb) - 1
            fill = (0xFF & ~ln) if sg else 0
            sflag = {1: "ldsb", 2: "ldsh", 4: "ldsw"}.get(nb) if sg else None
            kw = dict(rs1=i.rs1, rd=i.rd, b_imm=1, imm=u64(i.imm), mem=1, ln=ln, fill=fill,
                      a_h=int(nb >= 2), a_w=int(nb >= 4), a_d=int(nb == 8))
            if sflag:
                kw[sflag] = 1
            row(**kw)
    elif n in STORE_INFO:
        nb = STORE_INFO[n]
        row(rs1=i.rs1, rs2=i.rs2, b_imm=1, imm=u64(i.imm), mem=1, st_w=1 << (nb.bit_length() - 1),
            a_h=int(nb >= 2), a_w=int(nb >= 4), a_d=int(nb == 8))
    else:
        raise AssertionError(n)
    return rows


def expand(code: dict[int, int], entry_pc: int) -> Program:
    pcs = sorted(code)
    instrs = {pc: decode(code[pc]) for pc in pcs}
    # pass 1: row counts -> head micro-PCs
    counts = {pc: len(expand_instr(instrs[pc], pc, lambda p: TRAP_UPC)) for pc in pcs}
    upc_of_pc: dict[int, int] = {}
    nxt = 2
    for pc in pcs:
        upc_of_pc[pc] = nxt
        nxt += counts[pc]

    def tgt_upc(p: int) -> int:
        return upc_of_pc.get(p, TRAP_UPC) if p % 4 == 0 else TRAP_UPC

    rom = [blank_row(), blank_row()]
    rom[HALTED_UPC].update(upc=HALTED_UPC, halted=1, rs1=10, seq=HALTED_UPC)
    rom[TRAP_UPC].update(upc=TRAP_UPC, trap=1, seq=TRAP_UPC)
    for pc in pcs:
        rows = expand_instr(instrs[pc], pc, tgt_upc)
        for k, r in enumerate(rows):
            u = len(rom)
            r["upc"], r["rpc"], r["head"] = u, pc, int(k == 0)
            sq = r.pop("_seq", None)
            if sq is not None:
                r["seq"] = sq
            elif k + 1 < len(rows):
                r["seq"] = u + 1
            else:
                r["seq"] = tgt_upc(pc + 4)
            rom.append(r)
    assert len(rom) == nxt
    assert entry_pc in upc_of_pc, "entry pc not in code"
    return Program(rom, COLUMNS, upc_of_pc, entry_pc, upc_of_pc[entry_pc], dict(code), dict(counts))


# ----------------------------------------------------------------------------
# Virtual machine
# ----------------------------------------------------------------------------

@dataclass
class VMResult:
    exit_code: int
    regs: list[int]          # 64 entries (32 architectural + 32 virtual)
    ram: dict[int, int]
    trace: list[dict]
    instret: int             # number of RV64I instructions retired (heads executed, HALT included)


class VirtualMachine:
    def __init__(self, program: Program, ram_words: dict[int, int], ram_log_words: int):
        self.p = program
        self.ram = {k: v & M64 for k, v in ram_words.items() if v}
        self.A = ram_log_words
        self.regs = [0] * 64
        self.upc = program.entry_upc

    def run(self, max_cycles: int) -> VMResult:
        trace: list[dict] = []
        instret = 0
        rom = self.p.rom
        while True:
            row = rom[self.upc]
            if row["halted"]:
                break
            if len(trace) >= max_cycles:
                raise Trap("max_cycles exceeded")
            instret += row["head"]
            trace.append(self.step(row))
        return VMResult(self.regs[10], list(self.regs), dict(self.ram), trace, instret)

    def run_padded(self, max_cycles: int) -> VMResult:
        """Run to HALT, then append HALTED cycles until the trace length is a power of two >= 4
        that exceeds the number of real cycles (so the final cycle is HALTED)."""
        res = self.run(max_cycles)
        t = 4
        while t < len(res.trace) + 1:
            t *= 2
        while len(res.trace) < t:
            res.trace.append(self.step(self.p.rom[HALTED_UPC]))
        return res

    def step(self, row: dict[str, int]) -> dict:
        regs = self.regs
        if row["trap"]:
            raise Trap("trap row reached")
        v1, v2 = regs[row["rs1"]], regs[row["rs2"]]
        if row["rs1"] == 0:
            v1 = 0
        if row["rs2"] == 0:
            v2 = 0
        if row["ecall"] and v2 != 0:
            raise Trap("unsupported ECALL")
        # RAM read (word 0 when no access)
        S0 = datapath(row, v1, v2, 0)["S"]
        ridx = 0
        if row["mem"]:
            if (row["a_h"] and S0 & 1) or (row["a_w"] and S0 & 2) or (row["a_d"] and S0 & 4):
                raise Trap("misaligned access")
            off = S0 - RAM_BASE
            if not (0 <= off < 8 << self.A):
                raise Trap("RAM access out of range")
            ridx = off >> 3
        rw = self.ram.get(ridx, 0)
        d = datapath(row, v1, v2, rw)
        rdv = d["rdv"]
        rd = row["rd"]
        rd_old = regs[rd]
        if rd == 0:
            assert rdv == 0, "x0 write must be zero"
        # store
        new = rw
        if row["st_w"]:
            new = store_apply(onehot_index(row["st_w"]), d["off"], rw, v2)
        if new:
            self.ram[ridx] = new
        else:
            self.ram.pop(ridx, None)
        regs[rd] = rdv
        regs[0] = 0
        # next micro-PC
        dynu = 0
        if row["jalr"]:
            target = d["S"] & ~1 & M64
            dynu = self.p.upc_of_pc.get(target)
            if dynu is None:
                raise Trap(f"jalr to non-code pc {target:#x}")
            nxt = dynu
        else:
            nxt = row["tgt"] if d["take"] else row["seq"]
        rec = dict(upc=row["upc"], rom=row, rs1=row["rs1"], rs2=row["rs2"], rd=rd, v1=v1, v2=v2,
                   rd_old=rd_old, rd_val=rdv, ram_idx=ridx, ram_old=rw, ram_new=new,
                   inc=rw ^ new, shift_kind=onehot_index(row["Q_hi"]),
                   shift_amt=onehot_index(row["Q_lo"]), shift_src=v1, shift_out=d["Y"],
                   store_width=onehot_index(row["st_w"]), store_off=d["off"], store_src=v2,
                   take=d["take"], dynu=dynu if row["jalr"] else 0, next_upc=nxt, dp=d)
        self.upc = nxt
        return rec


def run_program(code, entry_pc, ram_words, ram_log_words, max_cycles=1 << 20) -> VMResult:
    prog = expand(code, entry_pc)
    return VirtualMachine(prog, ram_words, ram_log_words).run(max_cycles)
