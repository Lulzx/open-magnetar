import random
import unittest

from openmagnetar import bytecode as bc
from openmagnetar import cpu_circuit as cpu
from openmagnetar import riscv
from openmagnetar.riscv import Machine, Trap, decode

from .asm import HALT, asm, li32, program

RAM = 0x8000_0000
A = 8


def run_both(instrs, ram=None, max_cycles=100000):
    code, entry = program(instrs)
    ram = ram or {}
    m = Machine(code, entry, ram, A).run(max_cycles)
    vm = bc.VirtualMachine(bc.expand(code, entry), ram, A).run_padded(max_cycles)
    return code, entry, m, vm


def prologue_ram_base(rd=1):
    # x1 = 0x8000_0000 (lui sign-extends, so build it with slli)
    return [("addi", rd, 0, 1), ("slli", rd, rd, 31)]


class TestDecoder(unittest.TestCase):
    def test_roundtrip_many(self):
        cases = [
            (("addi", 5, 6, -1), "ADDI", dict(rd=5, rs1=6, imm=-1)),
            (("addi", 5, 6, 2047), "ADDI", dict(imm=2047)),
            (("sub", 1, 2, 3), "SUB", dict(rd=1, rs1=2, rs2=3)),
            (("sltu", 31, 30, 29), "SLTU", dict(rd=31, rs1=30, rs2=29)),
            (("srai", 3, 4, 63), "SRAI", dict(imm=63)),
            (("srli", 3, 4, 1), "SRLI", dict(imm=1)),
            (("slli", 3, 4, 33), "SLLI", dict(imm=33)),
            (("sraiw", 3, 4, 31), "SRAIW", dict(imm=31)),
            (("slliw", 3, 4, 5), "SLLIW", dict(imm=5)),
            (("addiw", 3, 4, -7), "ADDIW", dict(imm=-7)),
            (("subw", 3, 4, 5), "SUBW", dict()),
            (("sraw", 3, 4, 5), "SRAW", dict()),
            (("lui", 7, 0xFFFFF), "LUI", dict(rd=7, imm=-4096)),
            (("lui", 7, 1), "LUI", dict(imm=4096)),
            (("auipc", 7, 0x12345), "AUIPC", dict(imm=0x12345000)),
            (("jal", 1, 2048), "JAL", dict(rd=1, imm=2048)),
            (("jal", 0, -4), "JAL", dict(imm=-4)),
            (("jal", 1, -(1 << 20)), "JAL", dict(imm=-(1 << 20))),
            (("jalr", 1, 2, -8), "JALR", dict(rd=1, rs1=2, imm=-8)),
            (("beq", 1, 2, -4096), "BEQ", dict(imm=-4096)),
            (("bne", 1, 2, 4094), "BNE", dict(imm=4094)),
            (("blt", 1, 2, 8), "BLT", dict(imm=8)),
            (("bge", 1, 2, -2), "BGE", dict(imm=-2)),
            (("bltu", 1, 2, 100), "BLTU", dict(imm=100)),
            (("bgeu", 1, 2, 2000), "BGEU", dict(imm=2000)),
            (("lb", 1, 2, -1), "LB", dict(imm=-1)),
            (("lhu", 1, 2, 6), "LHU", dict(imm=6)),
            (("lwu", 1, 2, 4), "LWU", dict(imm=4)),
            (("ld", 1, 2, 2040), "LD", dict(imm=2040)),
            (("sb", 1, 2, -1), "SB", dict(rs1=2, rs2=1, imm=-1)),
            (("sh", 1, 2, 2), "SH", dict(imm=2)),
            (("sw", 1, 2, -2048), "SW", dict(imm=-2048)),
            (("sd", 1, 2, 2047), "SD", dict(imm=2047)),
            (("fence",), "FENCE", {}),
            (("ecall",), "ECALL", {}),
            (("ebreak",), "EBREAK", {}),
        ]
        for ins, name, fields in cases:
            i = decode(asm(*ins))
            self.assertEqual(i.name, name, ins)
            for k, v in fields.items():
                self.assertEqual(getattr(i, k), v, (ins, k))

    def test_illegal(self):
        for w in (0x00000000, 0xFFFFFFFF, 0x02000033,  # MUL (M ext)
                  0x0000100F,                           # FENCE.I
                  0x00001067,                           # JALR f3!=0
                  0x00004003 | (7 << 12),               # load f3=7
                  0x40001013,                           # slli with bad funct6
                  0x00200073):                          # not ECALL/EBREAK
            self.assertEqual(decode(w).name, "ILLEGAL", hex(w))

    def test_random_regs(self):
        rng = random.Random(1)
        for _ in range(200):
            rd, a, b = (rng.randrange(32) for _ in range(3))
            i = decode(asm("xor", rd, a, b))
            self.assertEqual((i.name, i.rd, i.rs1, i.rs2), ("XOR", rd, a, b))


class TestInterpreter(unittest.TestCase):
    def test_fibonacci(self):
        # x5=0,x6=1; loop 10 times: t=x5+x6; x5=x6; x6=t. fib(10)=55
        prog = [("addi", 5, 0, 0), ("addi", 6, 0, 1), ("addi", 7, 0, 10),
                ("add", 28, 5, 6), ("addi", 5, 6, 0), ("addi", 6, 28, 0),
                ("addi", 7, 7, -1), ("bne", 7, 0, -16),
                ("addi", 10, 5, 0)] + HALT
        _, _, m, vm = run_both(prog)
        self.assertEqual(m.exit_code, 55)
        self.assertEqual(vm.exit_code, 55)
        # every instruction here is a single virtual cycle (loop body: 5 cycles)
        self.assertEqual(vm.instret, 3 + 10 * 5 + 3)
        real = [r for r in vm.trace if not r["rom"]["halted"]]
        self.assertEqual(len(real), vm.instret)

    def test_alu(self):
        prog = (li32(5, 0x7FFFFFFF) + li32(6, -5) + [
            ("addw", 7, 5, 5), ("subw", 8, 6, 5), ("slt", 9, 6, 5), ("sltu", 11, 6, 5),
            ("sltiu", 12, 5, -1), ("slti", 13, 6, -4), ("xori", 14, 6, -1), ("ori", 15, 5, 0x555),
            ("andi", 16, 6, 0xFF), ("sub", 17, 0, 5), ("add", 18, 6, 6),
            ("addi", 10, 0, 0)] + HALT)
        _, _, m, vm = run_both(prog)
        self.assertEqual(m.regs[7], 0xFFFFFFFFFFFFFFFE)
        self.assertEqual(m.regs[9], 1)
        self.assertEqual(m.regs[11], 0)
        self.assertEqual(m.regs[12], 1)
        self.assertEqual(m.regs[13], 1)
        self.assertEqual(m.regs[14], 4)
        self.assertEqual(m.regs[16], 0xFB)
        self.assertEqual(m.regs[:32], vm.regs[:32])

    def test_shifts_all(self):
        rng = random.Random(5)
        vals = [0x8000000000000001, 0x00000000F0F0F0F1, 0x123456789ABCDEF0, 0xFFFFFFFF80000000, 1, 0]
        for rr in ("sll", "srl", "sra", "sllw", "srlw", "sraw"):
            for v in vals:
                for amt in (0, 1, 5, 17, 31, 32, 33, 63):
                    prog = [("addi", 5, 0, 1), ("slli", 5, 5, 63), ("addi", 6, 0, amt)]
                    # build v in x7 from halves
                    prog += li32(7, v >> 32) + [("slli", 7, 7, 32)] + li32(8, v & 0xFFFFFFFF)
                    prog += [("slli", 8, 8, 32), ("srli", 8, 8, 32), ("or_", 7, 7, 8)]
                    prog += [(rr, 10, 7, 6), ("add", 10, 10, 0)] + HALT
                    _, _, m, vm = run_both(prog)
                    ref = riscv.alu(rr.upper(), v, amt)
                    self.assertEqual(m.exit_code, ref, (rr, hex(v), amt))
                    self.assertEqual(vm.exit_code, ref, (rr, hex(v), amt))
        for ri, mx in (("slli", 63), ("srli", 63), ("srai", 63), ("slliw", 31), ("srliw", 31), ("sraiw", 31)):
            for v in vals:
                for amt in (0, 1, 7, mx):
                    prog = li32(7, v >> 32) + [("slli", 7, 7, 32)] + li32(8, v & 0xFFFFFFFF)
                    prog += [("slli", 8, 8, 32), ("srli", 8, 8, 32), ("or_", 7, 7, 8)]
                    prog += [(ri, 10, 7, amt)] + HALT
                    _, _, m, vm = run_both(prog)
                    ref = riscv.alu(ri.upper(), v, amt)
                    self.assertEqual(m.exit_code, ref, (ri, hex(v), amt))
                    self.assertEqual(vm.exit_code, ref, (ri, hex(v), amt))

    def test_shift_cycle_counts(self):
        p = bc.expand(*program([("sll", 3, 4, 5), ("sllw", 3, 4, 5), ("slli", 3, 4, 5), ("add", 1, 2, 3)] + HALT))
        cyc = [p.cycles_of_pc[pc] for pc in sorted(p.cycles_of_pc)]
        self.assertEqual(cyc[:4], [6, 5, 1, 1])

    def test_loads_stores_all_widths(self):
        base = prologue_ram_base()
        # store a known doubleword then load every width/offset
        data = 0x8899AABBCCDDEEFF
        prog = base + li32(2, data >> 32) + [("slli", 2, 2, 32)] + li32(3, data & 0xFFFFFFFF)
        prog += [("slli", 3, 3, 32), ("srli", 3, 3, 32), ("or_", 2, 2, 3), ("sd", 2, 1, 0)]
        n_ld = 0
        for op, step, nb in (("lb", 1, 1), ("lbu", 1, 1), ("lh", 2, 2), ("lhu", 2, 2),
                             ("lw", 4, 4), ("lwu", 4, 4), ("ld", 8, 8)):
            for off in range(0, 8, step):
                prog += [(op, 10, 1, off), ("sd", 10, 1, 64 + 8 * n_ld)]
                n_ld += 1
        # sub-word stores into a zeroed word: sb at every offset, sh, sw
        prog += [("addi", 4, 0, -1)]
        for off in range(8):
            prog += [("sb", 4, 1, 512 + off)]
        prog += [("sh", 4, 1, 520 + 2), ("sw", 4, 1, 528 + 4), ("sd", 4, 1, 536)]
        prog += [("addi", 5, 0, 0x7F), ("sb", 5, 1, 520), ("sh", 5, 1, 528), ("sw", 5, 1, 544 + 4)]
        prog += [("addi", 10, 0, 3)] + HALT
        _, _, m, vm = run_both(prog)
        self.assertEqual(m.ram, vm.ram)
        self.assertEqual(m.regs[:32], vm.regs[:32])
        w = lambda a: m.ram.get((a - 0) >> 3, 0)
        self.assertEqual(w(512), 0xFFFFFFFFFFFFFFFF)
        self.assertEqual(w(520), 0x00000000FFFF007F)
        self.assertEqual(w(528), 0xFFFFFFFF0000007F | 0)  # sw at +4 then sh at 0 -> low half 0x007F

    def test_signext_values(self):
        base = prologue_ram_base()
        data = 0x8899AABBCCDDEEFF
        prog = base + li32(2, data >> 32) + [("slli", 2, 2, 32)] + li32(3, data & 0xFFFFFFFF)
        prog += [("slli", 3, 3, 32), ("srli", 3, 3, 32), ("or_", 2, 2, 3), ("sd", 2, 1, 0)]
        for op, off, want in (("lb", 7, 0xFFFFFFFFFFFFFF88), ("lbu", 7, 0x88), ("lh", 6, 0xFFFFFFFFFFFF8899),
                              ("lhu", 6, 0x8899), ("lw", 4, 0xFFFFFFFF8899AABB), ("lwu", 4, 0x8899AABB),
                              ("lw", 0, 0xFFFFFFFFCCDDEEFF), ("lb", 1, 0xFFFFFFFFFFFFFFEE),
                              ("ld", 0, data), ("lh", 2, 0xFFFFFFFFFFFFCCDD)):
            p = prog + [(op, 10, 1, off)] + HALT
            _, _, m, vm = run_both(p)
            self.assertEqual(m.exit_code, want, (op, off))
            self.assertEqual(vm.exit_code, want, (op, off))

    def test_branches(self):
        # each pair: (op, a, b, taken)
        cases = [("beq", 5, 5, 1), ("beq", 5, 6, 0), ("bne", 5, 6, 1), ("bne", 5, 5, 0),
                 ("blt", -1, 1, 1), ("blt", 1, -1, 0), ("bge", -1, 1, 0), ("bge", 3, 3, 1),
                 ("bltu", -1, 1, 0), ("bltu", 1, -1, 1), ("bgeu", -1, 1, 1), ("bgeu", 2, 3, 0)]
        for op, a, b, taken in cases:
            prog = [("addi", 5, 0, a), ("addi", 6, 0, b), (op, 5, 6, 12),
                    ("addi", 10, 0, 0), ("jal", 0, 8), ("addi", 10, 0, 1)] + HALT
            # fix: for beq with a/b regs we need regs 5,6; branch compares x5,x6
            _, _, m, vm = run_both(prog)
            self.assertEqual(m.exit_code, taken, (op, a, b))
            self.assertEqual(vm.exit_code, taken, (op, a, b))

    def test_jal_jalr_lui_auipc(self):
        prog = [("jal", 1, 12),                 # 0x1000: ra=0x1004, jump to 0x100c
                ("addi", 10, 0, 99),            # 0x1004 (skipped first time)
                ("jal", 0, 16),                 # 0x1008 -> 0x1018
                ("addi", 5, 1, 0),              # 0x100c: x5 = ra
                ("jalr", 6, 1, 0),              # 0x1010: x6 = 0x1014; jump to 0x1004
                ("addi", 10, 0, 0),             # 0x1014 (unreached)
                ("auipc", 7, 1),                # 0x1018: x7 = 0x1018 + 0x1000
                ("lui", 8, 0x80000),            # x8 = 0xFFFFFFFF80000000
                ("jalr", 0, 7, 1),              # to (0x2018+1)&~1 -> not code => handled below
                ]
        # jalr to non-code is a trap: use a well-formed ending instead
        prog = prog[:-1] + [("addi", 9, 0, 0)] + HALT
        _, _, m, vm = run_both(prog)
        self.assertEqual(m.regs[5], 0x1004)
        self.assertEqual(m.regs[6], 0x1014)
        self.assertEqual(m.regs[7], 0x2018)
        self.assertEqual(m.regs[8], 0xFFFFFFFF80000000)
        self.assertEqual(m.exit_code, 99)
        self.assertEqual(m.regs[:32], vm.regs[:32])
        self.assertEqual(vm.exit_code, 99)

    def test_jalr_clears_low_bit(self):
        prog = [("addi", 5, 0, 0x7F), ("slli", 5, 5, 5), ("addi", 5, 5, 0x1D),  # 0xFE0+0x1D? computed below
                ]
        # target = 0x1000 + 4*k; load via addi: x5 = 0x1011 -> jalr clears bit0 -> 0x1010
        prog = [("addi", 5, 0, 0x7FF), ("addi", 5, 5, 0x7FF), ("addi", 5, 5, 0x7FF), ("addi", 5, 5, 0x7FF),
                ("addi", 5, 5, 0x7FF), ("addi", 5, 5, 0x7FF), ("addi", 5, 5, 0x7FF), ("addi", 5, 5, 0x7FF)]
        # simpler: use auipc
        prog = [("auipc", 5, 0), ("jalr", 0, 5, 13),   # target 0x100d -> 0x100c
                ("addi", 10, 0, 7),                    # 0x1008 (skipped)
                ("addi", 10, 0, 5)] + HALT             # 0x100c
        _, _, m, vm = run_both(prog)
        self.assertEqual(m.exit_code, 5)
        self.assertEqual(vm.exit_code, 5)

    def test_traps(self):
        for ins in ([("ebreak",)], [("addi", 17, 0, 1), ("ecall",)], [("lw", 1, 0, 0)],
                    [("addi", 1, 0, 1), ("slli", 1, 1, 31), ("lw", 2, 1, 1)]):
            code, entry = program(ins + HALT)
            with self.assertRaises(Trap):
                Machine(code, entry, {}, A).run(100)
            with self.assertRaises(Trap):
                bc.VirtualMachine(bc.expand(code, entry), {}, A).run(100)

    def test_x0_and_fence(self):
        prog = [("addi", 0, 0, 5), ("fence",), ("add", 0, 0, 0), ("addi", 10, 0, 0)] + HALT
        _, _, m, vm = run_both(prog)
        self.assertEqual(m.regs[0], 0)
        self.assertEqual(vm.regs[0], 0)


class TestVMvsMachine(unittest.TestCase):
    def test_random_programs(self):
        rng = random.Random(42)
        regs = list(range(1, 8))
        ops_rr = ["add", "sub", "xor", "or_", "and_", "slt", "sltu", "sll", "srl", "sra",
                  "addw", "subw", "sllw", "srlw", "sraw"]
        ops_i = ["addi", "slti", "sltiu", "xori", "ori", "andi", "addiw"]
        for trial in range(25):
            prog = prologue_ram_base(1)
            for r in regs[1:]:
                prog += li32(r, rng.getrandbits(32))
            for _ in range(30):
                k = rng.randrange(6)
                if k < 2:
                    prog.append((rng.choice(ops_rr), rng.choice(regs[1:]), rng.choice(regs[1:]), rng.choice(regs[1:])))
                elif k == 2:
                    prog.append((rng.choice(ops_i), rng.choice(regs[1:]), rng.choice(regs[1:]), rng.randrange(-2048, 2048)))
                elif k == 3:
                    prog.append((rng.choice(["slli", "srli", "srai"]), rng.choice(regs[1:]), rng.choice(regs[1:]), rng.randrange(64)))
                elif k == 4:
                    w = rng.choice([("sb", 1, 1), ("sh", 2, 2), ("sw", 4, 4), ("sd", 8, 8)])
                    prog.append((w[0], rng.choice(regs[1:]), 1, w[1] * rng.randrange(0, 8 // w[1]) + 8 * rng.randrange(4)))
                else:
                    w = rng.choice([("lb", 1), ("lbu", 1), ("lh", 2), ("lhu", 2), ("lw", 4), ("lwu", 4), ("ld", 8)])
                    prog.append((w[0], rng.choice(regs[1:]), 1, w[1] * rng.randrange(0, 8 // w[1]) + 8 * rng.randrange(4)))
            prog += [("add", 10, 2, 3)] + HALT
            _, _, m, vm = run_both(prog)
            self.assertEqual(m.exit_code, vm.exit_code)
            self.assertEqual(m.regs[:32], vm.regs[:32])
            self.assertEqual(m.ram, vm.ram)
            self.assertEqual(m.instret, vm.instret)
        self.assertTrue(len(vm.trace) & (len(vm.trace) - 1) == 0)

    def test_trace_fields(self):
        prog = [("addi", 5, 0, 3), ("sll", 6, 5, 5), ("addi", 10, 6, 0)] + HALT
        _, _, m, vm = run_both(prog)
        t = vm.trace
        self.assertEqual(t[1]["rd"], 32)          # first shift stage writes the temp register
        self.assertEqual(t[1]["shift_kind"], 0)
        self.assertEqual(t[1]["shift_amt"], 1)
        self.assertEqual(vm.exit_code, 24)
        for rec in t:
            if rec["rd"] == 0:
                self.assertEqual(rec["rd_val"], 0)


def make_trace(prog, ram=None, max_cycles=100000):
    code, entry = program(prog)
    p = bc.expand(code, entry)
    vm = bc.VirtualMachine(p, ram or {}, A).run_padded(max_cycles)
    return p, vm


class TestCircuit(unittest.TestCase):
    PAR = cpu.Params(ram_log_words=A)

    def prog_mix(self):
        base = prologue_ram_base(1)
        return (base + li32(2, 0x89ABCDEF) + li32(3, 5) + [
            ("sd", 2, 1, 0), ("lb", 4, 1, 3), ("lhu", 5, 1, 2), ("lw", 6, 1, 0),
            ("sb", 3, 1, 9), ("sh", 2, 1, 10), ("sw", 2, 1, 12),
            ("sll", 7, 2, 3), ("srlw", 8, 2, 3), ("sraw", 9, 2, 3), ("srai", 11, 2, 4),
            ("sub", 12, 3, 2), ("slt", 13, 2, 3), ("sltu", 14, 3, 2), ("subw", 15, 3, 2),
            ("xor", 16, 2, 3), ("or_", 17, 2, 3), ("and_", 18, 2, 3),
            ("beq", 3, 3, 8), ("addi", 31, 0, 1),
            ("bltu", 3, 2, 8), ("addi", 31, 0, 2),
            ("auipc", 19, 0), ("jalr", 20, 19, 12), ("addi", 31, 0, 3),
            ("addi", 10, 6, 0)] + HALT)

    def honest(self):
        p, vm = make_trace(self.prog_mix())
        W = cpu.witness(vm.trace, self.PAR)
        pub = cpu.public_inputs(p, vm.exit_code)
        return p, vm, W, pub

    def test_layout(self):
        segs = cpu.layout(self.PAR)
        spans = sorted((s.offset, s.offset + (1 << s.log_size)) for s in segs)
        for (a0, a1), (b0, b1) in zip(spans, spans[1:]):
            self.assertLessEqual(a1, b0)
        for s in segs:
            self.assertEqual(s.offset % (1 << s.log_size), 0)
        self.assertLessEqual(spans[-1][1], cpu.num_w_cols(self.PAR))
        owners = {s.owner for s in segs}
        self.assertTrue({"mosaic", "twist-reg", "twist-ram", "shout-bytecode", "router-shift"} <= owners)

    def test_honest_accepted(self):
        p, vm, W, pub = self.honest()
        self.assertEqual(cpu.violations(W, pub, self.PAR, p), [])
        self.assertTrue(cpu.check(W, pub, self.PAR, p))

    def test_other_programs_accepted(self):
        for prog in ([("addi", 10, 0, 9)] + HALT,
                     [("addi", 5, 0, 0), ("addi", 6, 0, 1), ("addi", 7, 0, 6), ("add", 28, 5, 6),
                      ("addi", 5, 6, 0), ("addi", 6, 28, 0), ("addi", 7, 7, -1), ("bne", 7, 0, -16),
                      ("addi", 10, 5, 0)] + HALT):
            p, vm = make_trace(prog)
            W = cpu.witness(vm.trace, self.PAR)
            self.assertTrue(cpu.check(W, cpu.public_inputs(p, vm.exit_code), self.PAR, p))

    def test_rejects_wrong_public(self):
        p, vm, W, pub = self.honest()
        self.assertFalse(cpu.check(W, dict(pub, exit_code=pub["exit_code"] ^ 1), self.PAR, p))
        self.assertFalse(cpu.check(W, dict(pub, entry_upc=pub["entry_upc"] + 1), self.PAR, p))

    def test_rejects_corruptions(self):
        p, vm, W, pub = self.honest()
        cc = cpu._built(self.PAR)[0]
        n = self.PAR.cycles
        tr = vm.trace

        def find(pred):
            for k, rec in enumerate(tr):
                if pred(rec):
                    return k
            raise AssertionError("no such cycle")

        cyc = {
            "add": find(lambda r: r["rom"]["c_add"] and not r["rom"]["sh_imm"] and not r["rom"]["bsel"]),
            "load": find(lambda r: r["rom"]["ln"] and r["rom"]["fill"]),
            "store": find(lambda r: r["rom"]["st_w"] and r["rom"]["st_w"] != 8),
            "shift": find(lambda r: r["rom"]["Q_lo"] and r["rom"]["bsel"]),
            "branch": find(lambda r: r["rom"]["br"]),
            "jalr": find(lambda r: r["rom"]["jalr"]),
            "slt": find(lambda r: r["rom"]["g_slt"]),
            "or": find(lambda r: r["rom"]["g"] and r["rom"]["e"]),
        }
        tests = [  # (field, bit, cycle key)
            ("cin", 5, "add"), ("T0", 3, "add"), ("rdv", 0, "add"), ("v1", 10, "add"),
            ("Bop", 20, "add"), ("AND", 2, "or"), ("T2", 7, "or"), ("x3", 3, "load"),
            ("m", 1, "load"), ("L", 40, "load"), ("rw", 5, "load"), ("fl", cpu.FL_POS["tb"], "load"),
            ("stc", 70, "store"), ("stc", 3, "store"), ("ridx", 0, "store"), ("off", 1, "store"),
            ("Gs", 4, "shift"), ("fl", cpu.FL_POS["cond"], "shift"), ("shsrc", 9, "shift"),
            ("Y", 12, "shift"), ("fl", cpu.FL_POS["take"], "branch"), ("nw", 40, "branch"),
            ("dynu", 3, "jalr"), ("fl", cpu.FL_POS["rdslt"], "slt"), ("fl", cpu.FL_POS["cout"], "slt"),
            ("upc", 1, "add"),            # micro-PC chain
            ("Dw", 0, "add"),
        ]
        # state-segment corruptions (X1/X2/X3 and the S_in/S_out ties)
        for name, bit in (("S_in", cpu.ST_UPC + 2), ("S_out", cpu.ST_UPC + 1), ("S_out", cpu.ST_HALT),
                          ("S_in", cpu.ST_EX + 3), ("S_out", cpu.ST_JF)):
            for j in (0, len(W) - 1):
                W2 = [list(r) for r in W]
                W2[j][cc.c(name, bit, 0)] ^= 1
                self.assertTrue(cpu.violations(W2, pub, self.PAR, p), (name, bit, j))
        kinds = set()
        for field, bit, key in tests:
            k = cyc[key]
            j, t = divmod(k, n)
            col = cc.c(field, bit, t)
            W2 = [list(r) for r in W]
            W2[j][col] ^= 1
            v = cpu.violations(W2, pub, self.PAR, p)
            self.assertTrue(v, (field, bit, key))
            kinds.add(field)
        self.assertGreaterEqual(len(kinds), 10)

    def test_rejects_rom_tamper_and_trap(self):
        p, vm, W, pub = self.honest()
        cc = cpu._built(self.PAR)[0]
        W2 = [list(r) for r in W]
        W2[0][cc.c("imm", 0, 0)] ^= 1      # decoded field disagrees with ROM[upc]
        self.assertFalse(cpu.check(W2, pub, self.PAR, p))
        # trap flag set in the witness is rejected by the relation itself
        W3 = [list(r) for r in W]
        W3[0][cc.c("rf", cpu.FLAG_POS["trap"], 0)] ^= 1
        self.assertTrue(cpu.violations(W3, pub, self.PAR))

    def test_not_halted_at_end_rejected(self):
        p, vm = make_trace([("addi", 5, 0, 1)] * 6 + [("addi", 10, 0, 1)] + HALT)
        tr = vm.trace[:4]
        self.assertFalse(tr[-1]["rom"]["halted"])
        W = cpu.witness(tr, self.PAR)
        self.assertFalse(cpu.check(W, cpu.public_inputs(p, vm.exit_code), self.PAR, p))

    def test_jalr_at_every_slot_alignment(self):
        for pad in range(4):
            prog = [("fence",)] * pad + [("auipc", 5, 0), ("jalr", 1, 5, 13), ("addi", 10, 0, 7),
                                         ("addi", 10, 0, 5)] + HALT
            p, vm = make_trace(prog)
            W = cpu.witness(vm.trace, self.PAR)
            pub = cpu.public_inputs(p, vm.exit_code)
            self.assertEqual(vm.exit_code, 5)
            self.assertTrue(cpu.check(W, pub, self.PAR, p), pad)
            # a prover that jumps to a different row for the dynamic target is rejected
            k = next(i for i, r in enumerate(vm.trace) if r["rom"]["jalr"])
            cc = cpu._built(self.PAR)[0]
            j, t = divmod(k, self.PAR.cycles)
            W2 = [list(r) for r in W]
            W2[j][cc.c("dynu", 2, t)] ^= 1
            self.assertFalse(cpu.check(W2, pub, self.PAR, p))

    def test_stats(self):
        s = cpu.stats(self.PAR)
        self.assertEqual(s["direct_bits_per_cycle"], 1108)
        self.assertEqual(s["NW"], 8192)


if __name__ == "__main__":
    unittest.main()
