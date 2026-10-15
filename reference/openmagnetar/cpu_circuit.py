"""CPU circuit: witness layout, the B-relation s1 and K-relation s2, witness generation, checker.

See docs/spec/10-cpu-circuit.md. All matrices are sparse: a matrix is a list of rows and a
row is a dict {column: coefficient}; coefficients are ints (B: always 1; K: the integer value
of the K element, per CONVENTIONS C1). Over characteristic 2, adding terms is XOR of coefficients.

Column space of one SIMD instance: z = (w, 1) with |w| = NW = 2^L and `1` at index NW
(n_x = 0, section 06 6.1). State crosses instance boundaries only through the two whole
segments S_in / S_out (section 06 6.6, relations X1-X3); public init/fin vectors are
`init_vector` / `fin_vector`.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from .bytecode import COLUMN_BY_NAME, FLAG_NAMES, HALTED_UPC, Program
from .field import K
from .riscv import M64

# --------------------------------------------------------------------------------------
# parameters and layout
# ----------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Params:
    ram_log_words: int = 16     # A, must satisfy 3 <= A <= 28
    log_cycles: int = 2         # c: 2^c cycles per SIMD instance

    @property
    def cycles(self) -> int:
        return 1 << self.log_cycles


@dataclass(frozen=True)
class Segment:
    name: str
    log_size: int          # per instance
    offset: int            # start column inside w (multiple of 2^log_size)
    kind: str              # 'direct' | 'virtual'
    owner: str             # 'mosaic' | 'twist-reg' | 'twist-ram' | 'shout-bytecode' | 'router-shift'
    width: int = 0         # bits per cycle (power of two)
    consumers: str = ""


# ROM flag word: bit positions
FLAG_POS: dict[str, int] = {n: i for i, n in enumerate(FLAG_NAMES)}
_o = len(FLAG_NAMES)
for _k in range(6):
    FLAG_POS[f"bsel{_k}"] = _o + _k
_o += 6
for _k in range(8):
    FLAG_POS[f"ln{_k}"] = _o + _k
_o += 8
for _k in range(8):
    FLAG_POS[f"fill{_k}"] = _o + _k
_o += 8
assert _o <= 64

FL_POS = {n: i for i, n in enumerate(
    ["cout", "cond", "p0", "p1", "p2", "p3", "p4", "p5", "u1", "u2", "rdslt", "eqres", "take",
     "tb", "th", "tw"])}

# (name, bits per cycle, kind, owner, consumers)
FIELDS = [
    # virtual, owned by memory-checking arguments
    ("v1", 64, "virtual", "twist-reg", "rs1 read value"),
    ("v2", 64, "virtual", "twist-reg", "rs2 read value"),
    ("rdv", 64, "virtual", "twist-reg", "rd write value"),
    ("rw", 64, "virtual", "twist-ram", "RAM word read (old word)"),
    ("ridx", 64, "virtual", "twist-ram", "RAM word index (0 if no access); 64 wide so its Spartan claim shares the point of rw (11)"),
    ("Y", 64, "virtual", "router-shift", "shift output"),
    # virtual, decoded bytecode fields
    ("imm", 64, "virtual", "shout-bytecode", ""),
    ("kc", 64, "virtual", "shout-bytecode", ""),
    ("rpc", 64, "virtual", "shout-bytecode", ""),
    ("upc", 32, "virtual", "shout-bytecode", ""),
    ("seq", 32, "virtual", "shout-bytecode", ""),
    ("tgt", 32, "virtual", "shout-bytecode", ""),
    ("rf", 64, "virtual", "shout-bytecode", "packed ROM flags (FLAG_POS)"),
    ("Q_lo", 64, "virtual", "shout-bytecode", "router-shift selector"),
    ("Q_hi", 8, "virtual", "shout-bytecode", "router-shift selector"),
    ("st_w", 4, "virtual", "shout-bytecode", "router-store selector"),
    # direct
    ("Bop", 64, "direct", "mosaic", "ALU B operand"),
    ("cin", 64, "direct", "mosaic", "adder carry-in vector c_0..c_63"),
    ("nw", 64, "direct", "mosaic", "zero-detect OR chain n_1..n_63"),
    ("AND", 64, "direct", "mosaic", "bitwise AND"),
    ("Dw", 32, "direct", "mosaic", "word sign-extension correction for bits 32..63"),
    ("T0", 64, "direct", "mosaic", "c_add * S'"),
    ("T1", 64, "direct", "mosaic", "T0 + e * XOR"),
    ("T2", 64, "direct", "mosaic", "T1 + g * AND"),
    ("Gs", 64, "direct", "mosaic", "cond * (S' + Y)"),
    ("shsrc", 64, "direct", "mosaic", "router-shift source copy of v1"),
    ("stc", 128, "direct", "mosaic", "router-store sources: [old RAM word | store source]"),
    ("off", 4, "direct", "mosaic", "low 3 address bits (+1 pad); router-store offset"),
    ("x1", 64, "direct", "mosaic", "load barrel stage 1"),
    ("x2", 64, "direct", "mosaic", "load barrel stage 2"),
    ("x3", 64, "direct", "mosaic", "load barrel stage 3 = rw >> 8*off"),
    ("m", 64, "direct", "mosaic", "load: lane-masked extracted word"),
    ("L", 64, "direct", "mosaic", "load result (zero on non-loads)"),
    ("fl", 16, "direct", "mosaic", "single-bit witnesses (FL_POS)"),
    ("dynu", 32, "direct", "mosaic", "dynamic JALR next micro-PC"),
    # per-instance state segments (width is per INSTANCE, not per cycle)
    ("S_in", 256, "direct", "mosaic", "carry-in state (06 6.6 S_in)"),
    ("S_out", 256, "direct", "mosaic", "carry-out state (06 6.6 S_out)"),
]
INSTANCE_FIELDS = {"S_in", "S_out"}
# state bit positions (S_in and S_out share the layout)
ST_UPC, ST_JT, ST_JF, ST_HALT, ST_EX = 0, 32, 96, 97, 98   # jt bit j (1..63) at ST_JT + j
FIELD = {f[0]: f for f in FIELDS}



@lru_cache(maxsize=None)
def _layout(params: Params):
    n = params.cycles
    segs = []
    for name, width, kind, owner, cons in sorted(
            FIELDS, key=lambda f: (-(f[1] if f[0] in INSTANCE_FIELDS else f[1] * n), f[0])):
        size = width if name in INSTANCE_FIELDS else width * n
        segs.append((name, size, kind, owner, width, cons))
    out, off = [], 0
    for name, size, kind, owner, width, cons in segs:
        assert off % size == 0
        out.append(Segment(name, size.bit_length() - 1, off, kind, owner, width, cons))
        off += size
    total = 1
    while total < off:
        total *= 2
    return tuple(out), off, total


def layout(params: Params = Params()) -> list[Segment]:
    return list(_layout(params)[0])


def used_bits(params: Params = Params()) -> int:
    return _layout(params)[1]


def num_w_cols(params: Params = Params()) -> int:
    """NW = |w| per SIMD instance (power of two); z has 2*NW entries."""
    return _layout(params)[2]


def _seg(params, name) -> Segment:
    for s in _layout(params)[0]:
        if s.name == name:
            return s
    raise KeyError(name)


class _Cols:
    def __init__(self, params: Params):
        self.p = params
        self.NW = num_w_cols(params)
        self.NZ = 2 * self.NW        # z = (w, 1) padded to 2*NW
        self.ONE = self.NW
        self.off = {s.name: s.offset for s in _layout(params)[0]}

    def c(self, field: str, bit: int, slot: int) -> int:
        w = FIELD[field][1]
        assert 0 <= bit < w
        if field in INSTANCE_FIELDS:
            return self.off[field] + bit
        assert 0 <= slot < self.p.cycles
        return self.off[field] + slot * w + bit


def _add(*ds):
    r: dict[int, int] = {}
    for d in ds:
        for k, v in d.items():
            nv = r.get(k, 0) ^ v
            if nv:
                r[k] = nv
            else:
                r.pop(k, None)
    return r


# --------------------------------------------------------------------------------------
# constraint construction
# --------------------------------------------------------------------------------------


class Structure:
    def __init__(self, name):
        self.name = name
        self.A: list[dict[int, int]] = []
        self.B: list[dict[int, int]] = []
        self.C: list[dict[int, int]] = []
        self.tags: list[str] = []

    def add(self, a, b, c, tag, NZ=0):
        self.A.append(a)
        self.B.append(b)
        self.C.append(c)
        self.tags.append(tag)

    def __len__(self):
        return len(self.A)


def _build(params: Params):
    cc = _Cols(params)
    A = params.ram_log_words
    assert 3 <= A <= 28
    s1, s2 = Structure("B"), Structure("K")
    ONE = {cc.ONE: 1}

    def one(c):
        return {c: 1}

    def f(name, t):                      # ROM flag column (virtual segment rf)
        return one(cc.c("rf", FLAG_POS[name], t))

    def fl(name, t):
        return one(cc.c("fl", FL_POS[name], t))

    def bitf(field, i, t):
        return one(cc.c(field, i, t))

    def S(i, t):                         # i-th adder sum bit (linear form)
        return _add(bitf("v1", i, t), bitf("Bop", i, t), f("sub", t), bitf("cin", i, t))

    def P(field, t, js, pos=None, src=None):
        """packed word: sum_j beta_{pos(j)} * col(field, src(j))."""
        d = {}
        for j in js:
            d = _add(d, {cc.c(field, j if src is None else src(j), t): 1 << (j if pos is None else pos(j))})
        return d

    def PF(fn, js):
        """packed word of linear forms fn(j) with coefficient beta_j."""
        d = {}
        for j in js:
            for k, v in fn(j).items():
                d = _add(d, {k: (1 << j) * v})
        return d

    R64 = range(64)
    n = params.cycles
    for t in range(n):
        last = t == n - 1
        # ---------------- B relation ----------------
        def b(a, bb, c, tag):
            s1.add(a, bb, c, tag, cc.NZ)

        for i in R64:
            cout = bitf("cin", i + 1, t) if i < 63 else fl("cout", t)
            if i == 63:
                cout = fl("cout", t)
            b(_add(bitf("v1", i, t), bitf("cin", i, t)),
              _add(bitf("Bop", i, t), f("sub", t), bitf("cin", i, t)),
              _add(cout, bitf("cin", i, t)), "adder-carry")
        # carry-out of bit 63 is c_64 = fl.cout; cin has 64 entries c_0..c_63
        b(ONE, _add(bitf("cin", 0, t), f("sub", t)), {}, "cin0")
        for i in range(3):
            b(ONE, _add(bitf("off", i, t), S(i, t)), {}, "off")
        for i in R64:
            b(bitf("v1", i, t), bitf("Bop", i, t), bitf("AND", i, t), "and")
        for i in range(1, 64):
            prev = S(0, t) if i == 1 else bitf("nw", i - 1, t)
            b(S(i, t), prev, _add(bitf("nw", i, t), S(i, t), prev), "zero-chain")
        for k in range(6):
            b(f(f"bsel{k}", t), bitf("v2", k, t), fl(f"p{k}", t), "shift-bit")
        b(ONE, _add(fl("cond", t), f("sh_imm", t), *[fl(f"p{k}", t) for k in range(6)]), {}, "cond")
        b(f("f_cmp", t), _add(ONE, fl("cout", t)), fl("u1", t), "cmp-u1")
        b(f("f_lts", t), _add(bitf("v1", 63, t), bitf("Bop", 63, t)), fl("u2", t), "cmp-u2")
        b(f("g_slt", t), _add(fl("u1", t), fl("u2", t)), fl("rdslt", t), "slt-bit")
        b(f("f_eq", t), _add(ONE, bitf("nw", 63, t)), fl("eqres", t), "eq")
        b(f("br", t), _add(fl("u1", t), fl("u2", t), fl("eqres", t), f("inv", t)), fl("take", t), "take")
        for nm, fg, bi in (("tb", "ldsb", 7), ("th", "ldsh", 15), ("tw", "ldsw", 31)):
            b(f(fg, t), bitf("x3", bi, t), fl(nm, t), "load-sign")
        b(f("trap", t), ONE, {}, "trap")
        for i, fg in enumerate(("a_h", "a_w", "a_d")):
            b(f(fg, t), S(i, t), {}, "align")
        if not last:
            b(f("jalr", t), _add(ONE, f("head", t + 1)), {}, "jalr-head")
        else:
            b(ONE, _add(one(cc.c("S_out", ST_JF, 0)), f("jalr", t)), {}, "jf-out")
            b(ONE, _add(one(cc.c("S_out", ST_HALT, 0)), f("halted", t)), {}, "halted-out")
        if t == 0:
            b(one(cc.c("S_in", ST_JF, 0)), _add(ONE, f("head", 0)), {}, "jf-in-head")

        # ---------------- K relation ----------------
        def k(a, bb, c, tag):
            s2.add(a, bb, c, tag, cc.NZ)

        k(f("b_imm", t), _add(P("imm", t, R64), P("v2", t, R64)),
          _add(P("Bop", t, R64), P("v2", t, R64)), "bop-mux")
        hi = range(32, 64)
        s31 = S(31, t)
        k(f("w", t), _add(PF(lambda j: S(j, t), hi), PF(lambda j: s31, hi)),
          P("Dw", t, range(32), pos=lambda j: j + 32), "dw")
        Sp = _add(PF(lambda j: S(j, t), R64), P("Dw", t, range(32), pos=lambda j: j + 32))
        X = PF(lambda j: _add(bitf("v1", j, t), bitf("Bop", j, t)), R64)
        k(f("c_add", t), Sp, P("T0", t, R64), "T0")
        k(f("e", t), X, _add(P("T1", t, R64), P("T0", t, R64)), "T1")
        k(f("g", t), P("AND", t, R64), _add(P("T2", t, R64), P("T1", t, R64)), "T2")
        k(fl("cond", t), _add(Sp, P("Y", t, R64)), P("Gs", t, R64), "Gs")
        k(ONE, _add(P("rdv", t, R64), P("T2", t, R64), P("Gs", t, R64), P("L", t, R64),
                    {cc.c("fl", FL_POS["rdslt"], t): 1}, P("kc", t, R64)), {}, "rd-val")
        k(ONE, _add(P("shsrc", t, R64), P("v1", t, R64)), {}, "shsrc-copy")
        k(ONE, _add(P("stc", t, R64), P("rw", t, R64)), {}, "st-old-copy")
        k(ONE, _add(P("stc", t, R64, src=lambda j: 64 + j), P("v2", t, R64)), {}, "st-src-copy")
        prevx = "rw"
        for st, sh in enumerate((8, 16, 32)):
            xs = f"x{st + 1}"
            k(bitf("off", st, t),
              _add(P(prevx, t, range(64 - sh), src=lambda j, sh=sh: j + sh), P(prevx, t, R64)),
              _add(P(xs, t, R64), P(prevx, t, R64)), "load-barrel")
            prevx = xs
        for ln in range(8):
            lane = range(8 * ln, 8 * ln + 8)
            k(f(f"ln{ln}", t), P("x3", t, lane), P("m", t, lane), "load-lane")
        fillw = {}
        for ln in range(8):
            fillw = _add(fillw, {cc.c("rf", FLAG_POS[f"fill{ln}"], t): 0xFF << (8 * ln)})
        k(_add(fl("tb", t), fl("th", t), fl("tw", t)), fillw, _add(P("L", t, R64), P("m", t, R64)), "load-sign-fill")
        k(f("mem", t), PF(lambda j: S(3 + j, t), range(A)), P("ridx", t, range(A)), "ridx")
        k(ONE, P("ridx", t, range(A, 64)), {}, "ridx-hi")
        win = _add(PF(lambda j: S(j, t), range(3 + A, 31)), PF(lambda j: S(j, t), range(31, 64)),
                   {cc.ONE: 1 << 31})
        k(f("mem", t), win, {}, "ram-window")
        R32 = range(32)
        nxt_upc = (P("S_out", 0, R32, src=lambda j: ST_UPC + j) if last else P("upc", t + 1, R32))
        k(fl("take", t), _add(P("tgt", t, R32), P("seq", t, R32)),
          _add(nxt_upc, P("seq", t, R32), P("dynu", t, R32)), "upc-next")
        k(_add(ONE, f("jalr", t)), P("dynu", t, R32), {}, "dynu-gate")
        if not last:
            k(f("jalr", t), _add(PF(lambda j: S(j, t), range(1, 64)), P("rpc", t + 1, range(1, 64))), {}, "jalr-target")
        else:
            k(f("jalr", t), PF(lambda j: S(j, t), range(1, 64)),
              P("S_out", 0, range(1, 64), src=lambda j: ST_JT + j), "jalr-target-out")
        k(f("halted", t), _add(P("v1", t, R64), PF(lambda j: one(cc.c("S_in", ST_EX + j, 0)), R64)), {}, "exit-code")
        k(f("ecall", t), P("v2", t, R64), {}, "ecall-a7")
    # slot-0 / instance-level rows tying S_in / S_out to the cycle fields
    k = lambda a, bb, c, tag: s2.add(a, bb, c, tag)
    k(ONE, _add(P("S_in", 0, range(32), src=lambda j: ST_UPC + j), P("upc", 0, range(32))), {}, "s-in-upc")
    k(one(cc.c("S_in", ST_JF, 0)),
      _add(P("S_in", 0, range(1, 64), src=lambda j: ST_JT + j), P("rpc", 0, range(1, 64))), {}, "s-in-jalr")
    k(ONE, _add(P("S_out", 0, range(64), src=lambda j: ST_EX + j), P("S_in", 0, range(64), src=lambda j: ST_EX + j)),
      {}, "ex-carry")
    return cc, s1, s2


@lru_cache(maxsize=None)
def _built(params: Params):
    return _build(params)


def build_s1(params: Params = Params()) -> Structure:
    return _built(params)[1]


def build_s2(params: Params = Params()) -> Structure:
    return _built(params)[2]


def init_vector(public: dict) -> list[int]:
    """Public init (06 6.6 X2): entry micro-PC, no pending JALR, not halted, exit code."""
    v = [0] * 256
    for i in range(32):
        v[ST_UPC + i] = (public["entry_upc"] >> i) & 1
    for i in range(64):
        v[ST_EX + i] = (public["exit_code"] >> i) & 1
    return v


def fin_vector(public: dict) -> list[int]:
    """Public fin (X3): next micro-PC = HALTED_UPC (0), no pending JALR, halted = 1, exit code."""
    v = [0] * 256
    v[ST_HALT] = 1
    for i in range(64):
        v[ST_EX + i] = (public["exit_code"] >> i) & 1
    return v


def stats(params: Params = Params()) -> dict:
    cc, s1, s2 = _built(params)
    n = params.cycles
    direct = sum(f[1] for f in FIELDS if f[2] == "direct" and f[0] not in INSTANCE_FIELDS)
    virt = sum(f[1] for f in FIELDS if f[2] == "virtual")
    direct_inst = sum(f[1] for f in FIELDS if f[0] in INSTANCE_FIELDS)
    return dict(cycles_per_instance=n, NW=cc.NW, used_bits=used_bits(params),
                direct_bits_per_cycle=direct, direct_bits_per_instance_state=direct_inst, virtual_bits_per_cycle=virt,
                s1_rows=len(s1), s2_rows=len(s2), s1_rows_per_cycle=len(s1) // n,
                s2_rows_per_cycle=len(s2) // n,
                s1_nnz=sum(len(r) for M in (s1.A, s1.B, s1.C) for r in M),
                s2_nnz=sum(len(r) for M in (s2.A, s2.B, s2.C) for r in M))


# --------------------------------------------------------------------------------------
# witness generation
# --------------------------------------------------------------------------------------


def _rom_fields(row: dict[str, int]) -> dict[str, int]:
    rf = 0
    for nm in FLAG_NAMES:
        rf |= row[nm] << FLAG_POS[nm]
    for k in range(6):
        rf |= ((row["bsel"] >> k) & 1) << FLAG_POS[f"bsel{k}"]
    for k in range(8):
        rf |= ((row["ln"] >> k) & 1) << FLAG_POS[f"ln{k}"]
        rf |= ((row["fill"] >> k) & 1) << FLAG_POS[f"fill{k}"]
    return dict(imm=row["imm"], kc=row["kc"], rpc=row["rpc"], upc=row["upc"], seq=row["seq"],
                tgt=row["tgt"], rf=rf, Q_lo=row["Q_lo"], Q_hi=row["Q_hi"], st_w=row["st_w"])


def cycle_fields(rec: dict) -> dict[str, int]:
    """All named field values of one cycle (field name -> integer, bit i = bit i of the field)."""
    d = rec["dp"]
    row = rec["rom"]
    fl = 0
    for nm, pos in FL_POS.items():
        if nm.startswith("p") and nm[1:].isdigit():
            v = d["p"][int(nm[1:])]
        else:
            v = d[nm]
        fl |= v << pos
    vals = dict(v1=rec["v1"], v2=rec["v2"], rdv=rec["rd_val"], rw=rec["ram_old"], ridx=rec["ram_idx"],
                Y=d["Y"], Bop=d["Bop"], cin=d["cin"], nw=d["nw"], AND=d["AND"], Dw=d["Dw"] >> 32,
                T0=d["T0"], T1=d["T1"], T2=d["T2"], Gs=d["Gs"], shsrc=rec["v1"],
                stc=rec["ram_old"] | (rec["v2"] << 64), off=d["off"], x1=d["x1"], x2=d["x2"],
                x3=d["x3"], m=d["m"], L=d["L"], fl=fl, dynu=rec["dynu"])
    vals.update(_rom_fields(row))
    return vals


def _state_out(trace, k, exit_code):
    """State after cycle k: next micro-PC, pending-JALR target, halted flag of cycle k, exit code."""
    rec = trace[k]
    row = rec["rom"]
    v = [0] * 256
    for i in range(32):
        v[ST_UPC + i] = (rec["next_upc"] >> i) & 1
    if row["jalr"]:
        tgt = rec["dp"]["S"] & ~1 & M64
        for j in range(1, 64):
            v[ST_JT + j] = (tgt >> j) & 1
        v[ST_JF] = 1
    v[ST_HALT] = row["halted"]
    for i in range(64):
        v[ST_EX + i] = (exit_code >> i) & 1
    return v


def _state_in(trace, k, n, exit_code):
    """State before cycle k (k = first cycle of an instance): the out-state of cycle k-1, or init."""
    if k == 0:
        v = [0] * 256
        for i in range(32):
            v[ST_UPC + i] = (trace[0]["upc"] >> i) & 1
        for i in range(64):
            v[ST_EX + i] = (exit_code >> i) & 1
        return v
    return _state_out(trace, k - 1, exit_code)


def witness(trace: list[dict], params: Params = Params(), exit_code: int | None = None) -> list[list[int]]:
    """W: one row (list of NW bits) per SIMD instance. len(trace) must be a multiple of 2^c.

    exit_code defaults to the value of a0 read by the final (HALTED) cycle."""
    cc = _built(params)[0]
    n = params.cycles
    if exit_code is None:
        exit_code = trace[-1]["v1"]
    assert len(trace) % n == 0 and trace
    rows = []
    for j in range(len(trace) // n):
        w = [0] * cc.NW
        for t in range(n):
            for name, val in cycle_fields(trace[j * n + t]).items():
                width = FIELD[name][1]
                base = cc.c(name, 0, t)
                for i in range(width):
                    if (val >> i) & 1:
                        w[base + i] = 1
        # state segments: S_in = state before the instance's first cycle, S_out after its last
        for name, st in (("S_in", _state_in(trace, j * n, n, exit_code)),
                         ("S_out", _state_out(trace, j * n + n - 1, exit_code))):
            for i, v in enumerate(st):
                if v:
                    w[cc.c(name, i, 0)] = 1
        rows.append(w)
    return rows


def public_inputs(program: Program, exit_code: int) -> dict:
    return dict(entry_upc=program.entry_upc, exit_code=exit_code & M64)


# --------------------------------------------------------------------------------------
# checker
# --------------------------------------------------------------------------------------


def _dot(row: dict[int, int], z):
    acc = 0
    for c, v in row.items():
        if z[c]:
            acc ^= v
    return acc


def violations(W: list[list[int]], public: dict, params: Params = Params(),
               program: Program | None = None) -> list[str]:
    """Return a list of violated constraints (empty means accepted)."""
    cc, s1, s2 = _built(params)
    NW = cc.NW
    q = len(W)
    out: list[str] = []
    zs = [list(W[j]) + [1] + [0] * (NW - 1) for j in range(q)]
    for j in range(q):
        z = zs[j]
        for r in range(len(s1)):
            a, b, c = (_dot(M[r], z) for M in (s1.A, s1.B, s1.C))
            if (a & b) != c:
                out.append(f"s1[{j}] row {r} ({s1.tags[r]})")
        for r in range(len(s2)):
            a, b, c = (_dot(M[r], z) for M in (s2.A, s2.B, s2.C))
            if (K(a) * K(b)).v != c:
                out.append(f"s2[{j}] row {r} ({s2.tags[r]})")
    st = lambda j, name: [W[j][cc.c(name, i, 0)] for i in range(256)]
    for j in range(1, q):
        if st(j, "S_in") != st(j - 1, "S_out"):
            out.append(f"X1[{j}]: S_in != previous S_out")
    if st(0, "S_in") != init_vector(public):
        out.append("X2: S_in(0) != init")
    if st(q - 1, "S_out") != fin_vector(public):
        out.append("X3: S_out(q-1) != fin")
    if program is not None:
        n = params.cycles
        for j in range(q):
            for t in range(n):
                get = lambda name: sum(W[j][cc.c(name, i, t)] << i for i in range(FIELD[name][1]))
                upc = get("upc")
                if upc >= len(program.rom):
                    out.append(f"rom[{j},{t}]: upc out of range")
                    continue
                want = _rom_fields(program.rom[upc])
                for name, val in want.items():
                    if get(name) != val:
                        out.append(f"rom[{j},{t}] {name}")
    return out


def check(W: list[list[int]], public: dict, params: Params = Params(),
          program: Program | None = None) -> bool:
    return not violations(W, public, params, program)
