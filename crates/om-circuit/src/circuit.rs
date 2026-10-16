//! Witness layout, the B-relation `s_1` and K-relation `s_2`, witness
//! generation, and the checker. Mirrors
//! `reference/openmagnetar/cpu_circuit.py`; see
//! `docs/spec/10-cpu-circuit.md`.
//!
//! All matrices are sparse: a row is a map `{column: coefficient}` with
//! coefficients in `K` (in `s_1` always `1`). Adding terms is XOR of
//! coefficients (characteristic 2).
//!
//! Column space of one SIMD instance: `z = (w, 1)` with `|w| = NW =
//! 2^13` and `1` at index `NW` (`n_x = 0`, spec 06 §6.1), zero-padded
//! to `2·NW`. State crosses instance boundaries only through the two
//! whole segments `S_in` / `S_out` (spec 06 §6.6, relations (X1)–(X3));
//! the public boundary vectors are [`init_vector`] / [`fin_vector`].

use std::collections::BTreeMap;

use om_field::K;
use om_isa::bytecode::{FLAG_NAMES, Program, Row, TraceRecord};
use om_isa::riscv::M64;
use om_spartan::r1cs::{R1CS, RelationField, SparseMatrix};
use om_spartan::spartan::SegmentKind;
use om_sumcheck::PackedBits;
use rayon::prelude::*;

// ---------------------------------------------------------------------------
// Parameters and layout
// ---------------------------------------------------------------------------

/// Circuit parameters (Python `Params`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Params {
    /// `A`: RAM holds `2^A` 64-bit words. Must satisfy `3 <= A <= 28`.
    pub ram_log_words: u32,
    /// `c`: `2^c` cycles per SIMD instance (spec 10.2 fixes `c = 2`).
    pub log_cycles: u32,
}

impl Default for Params {
    fn default() -> Self {
        Params {
            ram_log_words: 16,
            log_cycles: 2,
        }
    }
}

impl Params {
    /// Cycles (slots) per SIMD instance.
    pub fn cycles(&self) -> usize {
        1usize << self.log_cycles
    }
}

/// The component a segment's claims are handed to (spec 10.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Owner {
    Mosaic,
    TwistReg,
    TwistRam,
    ShoutBytecode,
    RouterShift,
}

impl Owner {
    /// The Python / vector spelling of this owner.
    pub fn as_str(self) -> &'static str {
        match self {
            Owner::Mosaic => "mosaic",
            Owner::TwistReg => "twist-reg",
            Owner::TwistRam => "twist-ram",
            Owner::ShoutBytecode => "shout-bytecode",
            Owner::RouterShift => "router-shift",
        }
    }

    /// Parse the Python / vector spelling, if it is one of the five.
    pub fn from_name(s: &str) -> Option<Self> {
        Some(match s {
            "mosaic" => Owner::Mosaic,
            "twist-reg" => Owner::TwistReg,
            "twist-ram" => Owner::TwistRam,
            "shout-bytecode" => Owner::ShoutBytecode,
            "router-shift" => Owner::RouterShift,
            _ => return None,
        })
    }
}

/// One aligned power-of-two block of columns of `w` (Python `Segment`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Segment {
    pub name: &'static str,
    /// Per-instance log size; the segment has `2^log_size` columns.
    pub log_size: usize,
    /// Start column inside `w` (a multiple of `2^log_size`).
    pub offset: usize,
    pub kind: SegmentKind,
    pub owner: Owner,
    /// Bits per cycle (a power of two); for `S_in`/`S_out`, bits per
    /// instance.
    pub width: usize,
    pub consumers: &'static str,
}

/// One per-cycle field (or per-instance state segment) before layout
/// (a row of Python's `FIELDS` table).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldDef {
    pub name: &'static str,
    /// Bits per cycle (per instance for `S_in`/`S_out`).
    pub width: usize,
    pub kind: SegmentKind,
    pub owner: Owner,
    pub consumers: &'static str,
}

const fn fd(
    name: &'static str,
    width: usize,
    kind: SegmentKind,
    owner: Owner,
    c: &'static str,
) -> FieldDef {
    FieldDef {
        name,
        width,
        kind,
        owner,
        consumers: c,
    }
}

use Owner::{Mosaic, RouterShift, ShoutBytecode, TwistRam, TwistReg};
use SegmentKind::{Direct, Virtual};

/// The 37 fields of the witness layout, in Python `FIELDS` order
/// (spec 10.3): `(name, bits per cycle, kind, owner, consumers)`.
pub const FIELDS: [FieldDef; 37] = [
    // virtual, owned by memory-checking arguments
    fd("v1", 64, Virtual, TwistReg, "rs1 read value"),
    fd("v2", 64, Virtual, TwistReg, "rs2 read value"),
    fd("rdv", 64, Virtual, TwistReg, "rd write value"),
    fd("rw", 64, Virtual, TwistRam, "RAM word read (old word)"),
    fd(
        "ridx",
        64,
        Virtual,
        TwistRam,
        "RAM word index (0 if no access); 64 wide so its Spartan claim shares the point of rw (11)",
    ),
    fd("Y", 64, Virtual, RouterShift, "shift output"),
    // virtual, decoded bytecode fields
    fd("imm", 64, Virtual, ShoutBytecode, ""),
    fd("kc", 64, Virtual, ShoutBytecode, ""),
    fd("rpc", 64, Virtual, ShoutBytecode, ""),
    fd("upc", 32, Virtual, ShoutBytecode, ""),
    fd("seq", 32, Virtual, ShoutBytecode, ""),
    fd("tgt", 32, Virtual, ShoutBytecode, ""),
    fd(
        "rf",
        64,
        Virtual,
        ShoutBytecode,
        "packed ROM flags (FLAG_POS)",
    ),
    fd("Q_lo", 64, Virtual, ShoutBytecode, "router-shift selector"),
    fd("Q_hi", 8, Virtual, ShoutBytecode, "router-shift selector"),
    fd("st_w", 4, Virtual, ShoutBytecode, "router-store selector"),
    // direct
    fd("Bop", 64, Direct, Mosaic, "ALU B operand"),
    fd("cin", 64, Direct, Mosaic, "adder carry-in vector c_0..c_63"),
    fd("nw", 64, Direct, Mosaic, "zero-detect OR chain n_1..n_63"),
    fd("AND", 64, Direct, Mosaic, "bitwise AND"),
    fd(
        "Dw",
        32,
        Direct,
        Mosaic,
        "word sign-extension correction for bits 32..63",
    ),
    fd("T0", 64, Direct, Mosaic, "c_add * S'"),
    fd("T1", 64, Direct, Mosaic, "T0 + e * XOR"),
    fd("T2", 64, Direct, Mosaic, "T1 + g * AND"),
    fd("Gs", 64, Direct, Mosaic, "cond * (S' + Y)"),
    fd(
        "shsrc",
        64,
        Direct,
        Mosaic,
        "router-shift source copy of v1",
    ),
    fd(
        "stc",
        128,
        Direct,
        Mosaic,
        "router-store sources: [old RAM word | store source]",
    ),
    fd(
        "off",
        4,
        Direct,
        Mosaic,
        "low 3 address bits (+1 pad); router-store offset",
    ),
    fd("x1", 64, Direct, Mosaic, "load barrel stage 1"),
    fd("x2", 64, Direct, Mosaic, "load barrel stage 2"),
    fd(
        "x3",
        64,
        Direct,
        Mosaic,
        "load barrel stage 3 = rw >> 8*off",
    ),
    fd("m", 64, Direct, Mosaic, "load: lane-masked extracted word"),
    fd("L", 64, Direct, Mosaic, "load result (zero on non-loads)"),
    fd("fl", 16, Direct, Mosaic, "single-bit witnesses (FL_POS)"),
    fd("dynu", 32, Direct, Mosaic, "dynamic JALR next micro-PC"),
    // per-instance state segments (width is per INSTANCE, not per cycle)
    fd("S_in", 256, Direct, Mosaic, "carry-in state (06 6.6 S_in)"),
    fd(
        "S_out",
        256,
        Direct,
        Mosaic,
        "carry-out state (06 6.6 S_out)",
    ),
];

/// The per-instance state segments (Python `INSTANCE_FIELDS`).
pub const INSTANCE_FIELDS: [&str; 2] = ["S_in", "S_out"];

/// Whether `name` is a per-instance state segment.
pub fn is_instance_field(name: &str) -> bool {
    INSTANCE_FIELDS.contains(&name)
}

// State bit positions; `S_in` and `S_out` share the layout (spec 10.9).
// `jt` bit `j` (1..63) sits at `ST_JT + j`.
/// State: micro-PC (bits 0..31).
pub const ST_UPC: usize = 0;
/// State: pending JALR target (bit `j` at `ST_JT + j`).
pub const ST_JT: usize = 32;
/// State: previous cycle was a JALR.
pub const ST_JF: usize = 96;
/// State: halted flag.
pub const ST_HALT: usize = 97;
/// State: exit code (bits 98..161).
pub const ST_EX: usize = 98;

/// Python `FIELD[name]`: the field definition, if it exists.
pub fn field(name: &str) -> Option<&'static FieldDef> {
    FIELDS.iter().find(|f| f.name == name)
}

/// Bit position of a flag in the packed ROM flag word `rf`
/// (Python `FLAG_POS[name]`): the 26 flags in [`FLAG_NAMES`] order,
/// then `bsel0..5`, `ln0..7`, `fill0..7` (48 used bits of 64).
pub fn flag_pos(name: &str) -> Option<usize> {
    if let Some(i) = FLAG_NAMES.iter().position(|&n| n == name) {
        return Some(i);
    }
    let sub = |prefix: &str, count: usize| -> Option<usize> {
        let k: usize = name.strip_prefix(prefix)?.parse().ok()?;
        (k < count).then_some(k)
    };
    if let Some(k) = sub("bsel", 6) {
        return Some(FLAG_NAMES.len() + k);
    }
    if let Some(k) = sub("ln", 8) {
        return Some(FLAG_NAMES.len() + 6 + k);
    }
    if let Some(k) = sub("fill", 8) {
        return Some(FLAG_NAMES.len() + 6 + 8 + k);
    }
    None
}

/// The single-bit witnesses of the `fl` segment, in `FL_POS` order.
pub const FL_NAMES: [&str; 16] = [
    "cout", "cond", "p0", "p1", "p2", "p3", "p4", "p5", "u1", "u2", "rdslt", "eqres", "take", "tb",
    "th", "tw",
];

/// Bit position of a single-bit witness in `fl` (Python `FL_POS[name]`).
pub fn fl_pos(name: &str) -> Option<usize> {
    FL_NAMES.iter().position(|&n| n == name)
}

fn fp(name: &str) -> usize {
    flag_pos(name).expect("flag name")
}

fn flp(name: &str) -> usize {
    fl_pos(name).expect("fl name")
}

/// `(segments, used_bits, NW)`: the buddy allocation "sort by
/// descending size, then name, place consecutively"; all sizes are
/// powers of two, so alignment is automatic (spec 10.3).
fn layout_full(params: &Params) -> (Vec<Segment>, usize, usize) {
    let n = params.cycles();
    let size = |f: &FieldDef| {
        if is_instance_field(f.name) {
            f.width
        } else {
            f.width * n
        }
    };
    let mut order: Vec<&FieldDef> = FIELDS.iter().collect();
    order.sort_by(|a, b| size(b).cmp(&size(a)).then(a.name.cmp(b.name)));
    let mut out = Vec::with_capacity(FIELDS.len());
    let mut off = 0usize;
    for f in order {
        let sz = size(f);
        assert!(off.is_multiple_of(sz), "segment {} misaligned", f.name);
        out.push(Segment {
            name: f.name,
            log_size: sz.trailing_zeros() as usize,
            offset: off,
            kind: f.kind,
            owner: f.owner,
            width: f.width,
            consumers: f.consumers,
        });
        off += sz;
    }
    (out, off, off.next_power_of_two())
}

/// The segment layout for `params` (Python `layout`). The order is the
/// segment-id order of `keygen.py`'s `Derived` (it enters the `vk`).
pub fn layout(params: &Params) -> Vec<Segment> {
    layout_full(params).0
}

/// Columns actually covered by segments (Python `used_bits`).
pub fn used_bits(params: &Params) -> usize {
    layout_full(params).1
}

/// `NW = |w|` per SIMD instance, a power of two; `z` has `2·NW` entries
/// (Python `num_w_cols`).
pub fn num_w_cols(params: &Params) -> usize {
    layout_full(params).2
}

/// The segment named `name`, if it exists (Python `_seg`).
pub fn segment(params: &Params, name: &str) -> Option<Segment> {
    layout(params).into_iter().find(|s| s.name == name)
}

/// Column arithmetic over one instance's `w` (Python `_Cols`).
#[derive(Debug, Clone)]
pub struct Cols {
    params: Params,
    /// `NW = |w|`.
    pub nw: usize,
    /// `|z| = 2·NW`.
    pub nz: usize,
    /// Column of the constant `1` (equal to `nw`).
    pub one: usize,
    offsets: BTreeMap<&'static str, usize>,
}

impl Cols {
    pub fn new(params: &Params) -> Cols {
        let nw = num_w_cols(params);
        Cols {
            params: *params,
            nw,
            nz: 2 * nw,
            one: nw,
            offsets: layout(params).iter().map(|s| (s.name, s.offset)).collect(),
        }
    }

    /// The parameters these columns were built for.
    pub fn params(&self) -> &Params {
        &self.params
    }

    /// Start column of segment `field` inside `w`.
    ///
    /// # Panics
    /// On an unknown field name (Python raises `KeyError`).
    pub fn offset(&self, field: &str) -> usize {
        self.offsets[field]
    }

    /// Column of `field`'s bit `bit` in slot `slot` (slot-major:
    /// `offset + slot·width + bit`). For the per-instance state
    /// segments the slot is ignored.
    ///
    /// # Panics
    /// On an unknown field, an out-of-range bit, or (per-cycle fields)
    /// an out-of-range slot, matching Python's `assert`s.
    pub fn c(&self, field: &str, bit: usize, slot: usize) -> usize {
        let w = self::field(field).expect("field name").width;
        assert!(bit < w, "bit out of range for {field}");
        if is_instance_field(field) {
            return self.offsets[field] + bit;
        }
        assert!(slot < self.params.cycles(), "slot out of range");
        self.offsets[field] + slot * w + bit
    }
}

/// A sparse linear form: `{column: coefficient}` (zero entries absent).
pub type SparseRow = BTreeMap<usize, K>;

/// XOR `other` into `acc` (Python `_add` of two forms).
fn add_into(acc: &mut SparseRow, other: &SparseRow) {
    for (&c, &v) in other {
        let e = acc.entry(c).or_insert(K::ZERO);
        *e += v;
        if e.is_zero() {
            acc.remove(&c);
        }
    }
}

/// XOR of any number of sparse linear forms (Python `_add`).
fn add(forms: &[SparseRow]) -> SparseRow {
    let mut r = SparseRow::new();
    for f in forms {
        add_into(&mut r, f);
    }
    r
}

// ---------------------------------------------------------------------------
// Constraint construction
// ---------------------------------------------------------------------------

/// One base R1CS structure under construction: the three sparse
/// matrices as row lists, plus a tag per row (Python `Structure`).
/// Rows are unpadded; padding to `2^rho` happens in
/// [`Structure::to_r1cs`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Structure {
    /// `"B"` for `s_1`, `"K"` for `s_2`.
    pub name: &'static str,
    pub a: Vec<SparseRow>,
    pub b: Vec<SparseRow>,
    pub c: Vec<SparseRow>,
    pub tags: Vec<&'static str>,
}

impl Structure {
    fn new(name: &'static str) -> Structure {
        Structure {
            name,
            a: Vec::new(),
            b: Vec::new(),
            c: Vec::new(),
            tags: Vec::new(),
        }
    }

    fn push(&mut self, a: SparseRow, b: SparseRow, c: SparseRow, tag: &'static str) {
        self.a.push(a);
        self.b.push(b);
        self.c.push(c);
        self.tags.push(tag);
    }

    /// Number of (unpadded) rows (Python `len(structure)`).
    pub fn len(&self) -> usize {
        self.a.len()
    }

    /// Whether the structure has no rows.
    pub fn is_empty(&self) -> bool {
        self.a.is_empty()
    }

    /// Total non-zero entries over `A`, `B`, `C`.
    pub fn nnz(&self) -> usize {
        [&self.a, &self.b, &self.c]
            .iter()
            .flat_map(|m| m.iter())
            .map(SparseRow::len)
            .sum()
    }

    /// Convert to an `om-spartan` [`R1CS`] padded to `2^rho × 2^nu`
    /// (the `keygen.py` `_matrix` conversion).
    ///
    /// # Panics
    /// If a row or column exceeds `(rho, nu)`, or a `B`-relation entry
    /// is not 0/1.
    pub fn to_r1cs(&self, field: RelationField, rho: usize, nu: usize) -> R1CS {
        let mat = |rows: &[SparseRow]| {
            SparseMatrix::new(
                rho,
                nu,
                rows.iter()
                    .enumerate()
                    .flat_map(|(r, row)| row.iter().map(move |(&c, &v)| ((r, c), v))),
            )
        };
        R1CS::new(field, rho, nu, mat(&self.a), mat(&self.b), mat(&self.c))
    }
}

/// The pair `(s_1, s_2)` as `om-spartan` relations sharing
/// `(rho, nu)`, derived as `keygen.py`'s `Derived` does:
/// `nu = log2(2·NW)`, `rho = ceil(log2(max(len(s_1), len(s_2))))`.
pub fn relations(params: &Params) -> (R1CS, R1CS) {
    let b = build(params);
    let nu = (2 * num_w_cols(params)).trailing_zeros() as usize;
    let max_rows = b.s1.len().max(b.s2.len());
    let rho = (usize::BITS - (max_rows - 1).leading_zeros()) as usize;
    (
        b.s1.to_r1cs(RelationField::B, rho, nu),
        b.s2.to_r1cs(RelationField::K, rho, nu),
    )
}

fn one(c: usize) -> SparseRow {
    SparseRow::from([(c, K::ONE)])
}

/// Row-builder state: column helpers mirroring the closures of
/// Python `_build`.
struct B<'a> {
    cc: &'a Cols,
}

impl B<'_> {
    /// ROM flag column (virtual segment `rf`).
    fn f(&self, name: &str, t: usize) -> SparseRow {
        one(self.cc.c("rf", fp(name), t))
    }
    fn fl(&self, name: &str, t: usize) -> SparseRow {
        one(self.cc.c("fl", flp(name), t))
    }
    fn bitf(&self, field: &str, i: usize, t: usize) -> SparseRow {
        one(self.cc.c(field, i, t))
    }
    /// `i`-th adder sum bit (a linear form).
    fn s(&self, i: usize, t: usize) -> SparseRow {
        add(&[
            self.bitf("v1", i, t),
            self.bitf("Bop", i, t),
            self.f("sub", t),
            self.bitf("cin", i, t),
        ])
    }
    /// Packed word `Σ_j β_{pos(j)} · col(field, src(j))` over `js`
    /// (Python `P` with identity `pos`/`src`).
    fn p(&self, field: &str, t: usize, js: impl IntoIterator<Item = usize>) -> SparseRow {
        self.px(field, t, js, |j| j, |j| j)
    }
    fn px(
        &self,
        field: &str,
        t: usize,
        js: impl IntoIterator<Item = usize>,
        pos: impl Fn(usize) -> usize,
        src: impl Fn(usize) -> usize,
    ) -> SparseRow {
        let mut d = SparseRow::new();
        for j in js {
            add_into(
                &mut d,
                &SparseRow::from([(self.cc.c(field, src(j), t), K::from_u128(1u128 << pos(j)))]),
            );
        }
        d
    }
    /// Packed word of linear forms: `Σ_j β_j · fn_(j)` (Python `PF`).
    fn pf(
        &self,
        js: impl IntoIterator<Item = usize>,
        mut fn_: impl FnMut(usize) -> SparseRow,
    ) -> SparseRow {
        let mut d = SparseRow::new();
        for j in js {
            for (c, v) in fn_(j) {
                add_into(
                    &mut d,
                    &SparseRow::from([(c, K::from_u128(1u128 << j) * v)]),
                );
            }
        }
        d
    }
}

/// Everything `_build` produces (Python `_built`): columns and both
/// structures.
#[derive(Debug, Clone)]
pub struct Built {
    pub cols: Cols,
    /// `s_1`, the B relation.
    pub s1: Structure,
    /// `s_2`, the K relation.
    pub s2: Structure,
}

/// Build both relations and the column map (Python `_build`/`_built`;
/// uncached — the structures are small).
///
/// # Panics
/// If `ram_log_words` is outside `3..=28` (Python `assert`).
pub fn build(params: &Params) -> Built {
    let cc = Cols::new(params);
    let a_words = params.ram_log_words as usize;
    assert!((3..=28).contains(&a_words), "A must satisfy 3 <= A <= 28");
    let mut s1 = Structure::new("B");
    let mut s2 = Structure::new("K");
    let one_form = one(cc.one);
    let h = B { cc: &cc };
    let n = params.cycles();

    for t in 0..n {
        let last = t == n - 1;
        // ---------------- B relation ----------------
        for i in 0..64 {
            let cout = if i < 63 {
                h.bitf("cin", i + 1, t)
            } else {
                h.fl("cout", t)
            };
            s1.push(
                add(&[h.bitf("v1", i, t), h.bitf("cin", i, t)]),
                add(&[h.bitf("Bop", i, t), h.f("sub", t), h.bitf("cin", i, t)]),
                add(&[cout, h.bitf("cin", i, t)]),
                "adder-carry",
            );
        }
        // carry-out of bit 63 is c_64 = fl.cout; cin has 64 entries c_0..c_63
        s1.push(
            one_form.clone(),
            add(&[h.bitf("cin", 0, t), h.f("sub", t)]),
            SparseRow::new(),
            "cin0",
        );
        for i in 0..3 {
            s1.push(
                one_form.clone(),
                add(&[h.bitf("off", i, t), h.s(i, t)]),
                SparseRow::new(),
                "off",
            );
        }
        for i in 0..64 {
            s1.push(
                h.bitf("v1", i, t),
                h.bitf("Bop", i, t),
                h.bitf("AND", i, t),
                "and",
            );
        }
        for i in 1..64 {
            let prev = if i == 1 {
                h.s(0, t)
            } else {
                h.bitf("nw", i - 1, t)
            };
            let si = h.s(i, t);
            s1.push(
                si.clone(),
                prev.clone(),
                add(&[h.bitf("nw", i, t), si, prev]),
                "zero-chain",
            );
        }
        for k in 0..6 {
            s1.push(
                h.f(&format!("bsel{k}"), t),
                h.bitf("v2", k, t),
                h.fl(&format!("p{k}"), t),
                "shift-bit",
            );
        }
        let mut cond_form = vec![h.fl("cond", t), h.f("sh_imm", t)];
        for k in 0..6 {
            cond_form.push(h.fl(&format!("p{k}"), t));
        }
        s1.push(one_form.clone(), add(&cond_form), SparseRow::new(), "cond");
        s1.push(
            h.f("f_cmp", t),
            add(&[one_form.clone(), h.fl("cout", t)]),
            h.fl("u1", t),
            "cmp-u1",
        );
        s1.push(
            h.f("f_lts", t),
            add(&[h.bitf("v1", 63, t), h.bitf("Bop", 63, t)]),
            h.fl("u2", t),
            "cmp-u2",
        );
        s1.push(
            h.f("g_slt", t),
            add(&[h.fl("u1", t), h.fl("u2", t)]),
            h.fl("rdslt", t),
            "slt-bit",
        );
        s1.push(
            h.f("f_eq", t),
            add(&[one_form.clone(), h.bitf("nw", 63, t)]),
            h.fl("eqres", t),
            "eq",
        );
        s1.push(
            h.f("br", t),
            add(&[
                h.fl("u1", t),
                h.fl("u2", t),
                h.fl("eqres", t),
                h.f("inv", t),
            ]),
            h.fl("take", t),
            "take",
        );
        for (nm, fg, bi) in [("tb", "ldsb", 7), ("th", "ldsh", 15), ("tw", "ldsw", 31)] {
            s1.push(h.f(fg, t), h.bitf("x3", bi, t), h.fl(nm, t), "load-sign");
        }
        s1.push(h.f("trap", t), one_form.clone(), SparseRow::new(), "trap");
        for (i, fg) in ["a_h", "a_w", "a_d"].iter().enumerate() {
            s1.push(h.f(fg, t), h.s(i, t), SparseRow::new(), "align");
        }
        if !last {
            s1.push(
                h.f("jalr", t),
                add(&[one_form.clone(), h.f("head", t + 1)]),
                SparseRow::new(),
                "jalr-head",
            );
        } else {
            s1.push(
                one_form.clone(),
                add(&[one(cc.c("S_out", ST_JF, 0)), h.f("jalr", t)]),
                SparseRow::new(),
                "jf-out",
            );
            s1.push(
                one_form.clone(),
                add(&[one(cc.c("S_out", ST_HALT, 0)), h.f("halted", t)]),
                SparseRow::new(),
                "halted-out",
            );
        }
        if t == 0 {
            s1.push(
                one(cc.c("S_in", ST_JF, 0)),
                add(&[one_form.clone(), h.f("head", 0)]),
                SparseRow::new(),
                "jf-in-head",
            );
        }

        // ---------------- K relation ----------------
        s2.push(
            h.f("b_imm", t),
            add(&[h.p("imm", t, 0..64), h.p("v2", t, 0..64)]),
            add(&[h.p("Bop", t, 0..64), h.p("v2", t, 0..64)]),
            "bop-mux",
        );
        let s31 = h.s(31, t);
        s2.push(
            h.f("w", t),
            add(&[h.pf(32..64, |j| h.s(j, t)), h.pf(32..64, |_| s31.clone())]),
            h.px("Dw", t, 0..32, |j| j + 32, |j| j),
            "dw",
        );
        let sp = add(&[
            h.pf(0..64, |j| h.s(j, t)),
            h.px("Dw", t, 0..32, |j| j + 32, |j| j),
        ]);
        let x = h.pf(0..64, |j| add(&[h.bitf("v1", j, t), h.bitf("Bop", j, t)]));
        s2.push(h.f("c_add", t), sp.clone(), h.p("T0", t, 0..64), "T0");
        s2.push(
            h.f("e", t),
            x,
            add(&[h.p("T1", t, 0..64), h.p("T0", t, 0..64)]),
            "T1",
        );
        s2.push(
            h.f("g", t),
            h.p("AND", t, 0..64),
            add(&[h.p("T2", t, 0..64), h.p("T1", t, 0..64)]),
            "T2",
        );
        s2.push(
            h.fl("cond", t),
            add(&[sp.clone(), h.p("Y", t, 0..64)]),
            h.p("Gs", t, 0..64),
            "Gs",
        );
        s2.push(
            one_form.clone(),
            add(&[
                h.p("rdv", t, 0..64),
                h.p("T2", t, 0..64),
                h.p("Gs", t, 0..64),
                h.p("L", t, 0..64),
                SparseRow::from([(cc.c("fl", flp("rdslt"), t), K::ONE)]),
                h.p("kc", t, 0..64),
            ]),
            SparseRow::new(),
            "rd-val",
        );
        s2.push(
            one_form.clone(),
            add(&[h.p("shsrc", t, 0..64), h.p("v1", t, 0..64)]),
            SparseRow::new(),
            "shsrc-copy",
        );
        s2.push(
            one_form.clone(),
            add(&[h.p("stc", t, 0..64), h.p("rw", t, 0..64)]),
            SparseRow::new(),
            "st-old-copy",
        );
        s2.push(
            one_form.clone(),
            add(&[
                h.px("stc", t, 0..64, |j| j, |j| 64 + j),
                h.p("v2", t, 0..64),
            ]),
            SparseRow::new(),
            "st-src-copy",
        );
        let mut prevx = "rw";
        for (st, sh) in [8usize, 16, 32].into_iter().enumerate() {
            let xs: &'static str = ["x1", "x2", "x3"][st];
            s2.push(
                h.bitf("off", st, t),
                add(&[
                    h.px(prevx, t, 0..64 - sh, |j| j, |j| j + sh),
                    h.p(prevx, t, 0..64),
                ]),
                add(&[h.p(xs, t, 0..64), h.p(prevx, t, 0..64)]),
                "load-barrel",
            );
            prevx = xs;
        }
        for ln in 0..8 {
            let lane = 8 * ln..8 * ln + 8;
            s2.push(
                h.f(&format!("ln{ln}"), t),
                h.p("x3", t, lane.clone()),
                h.p("m", t, lane),
                "load-lane",
            );
        }
        let mut fillw = SparseRow::new();
        for ln in 0..8 {
            add_into(
                &mut fillw,
                &SparseRow::from([(
                    cc.c("rf", fp(&format!("fill{ln}")), t),
                    K::from_u128(0xFFu128 << (8 * ln)),
                )]),
            );
        }
        s2.push(
            add(&[h.fl("tb", t), h.fl("th", t), h.fl("tw", t)]),
            fillw,
            add(&[h.p("L", t, 0..64), h.p("m", t, 0..64)]),
            "load-sign-fill",
        );
        s2.push(
            h.f("mem", t),
            h.pf(0..a_words, |j| h.s(3 + j, t)),
            h.p("ridx", t, 0..a_words),
            "ridx",
        );
        s2.push(
            one_form.clone(),
            h.p("ridx", t, a_words..64),
            SparseRow::new(),
            "ridx-hi",
        );
        let win = add(&[
            h.pf(3 + a_words..31, |j| h.s(j, t)),
            h.pf(31..64, |j| h.s(j, t)),
            SparseRow::from([(cc.one, K::from_u128(1u128 << 31))]),
        ]);
        s2.push(h.f("mem", t), win, SparseRow::new(), "ram-window");
        let nxt_upc = if last {
            h.px("S_out", 0, 0..32, |j| j, |j| ST_UPC + j)
        } else {
            h.p("upc", t + 1, 0..32)
        };
        s2.push(
            h.fl("take", t),
            add(&[h.p("tgt", t, 0..32), h.p("seq", t, 0..32)]),
            add(&[nxt_upc, h.p("seq", t, 0..32), h.p("dynu", t, 0..32)]),
            "upc-next",
        );
        s2.push(
            add(&[one_form.clone(), h.f("jalr", t)]),
            h.p("dynu", t, 0..32),
            SparseRow::new(),
            "dynu-gate",
        );
        if !last {
            s2.push(
                h.f("jalr", t),
                add(&[h.pf(1..64, |j| h.s(j, t)), h.p("rpc", t + 1, 1..64)]),
                SparseRow::new(),
                "jalr-target",
            );
        } else {
            s2.push(
                h.f("jalr", t),
                h.pf(1..64, |j| h.s(j, t)),
                h.px("S_out", 0, 1..64, |j| j, |j| ST_JT + j),
                "jalr-target-out",
            );
        }
        s2.push(
            h.f("halted", t),
            add(&[
                h.p("v1", t, 0..64),
                h.pf(0..64, |j| one(cc.c("S_in", ST_EX + j, 0))),
            ]),
            SparseRow::new(),
            "exit-code",
        );
        s2.push(
            h.f("ecall", t),
            h.p("v2", t, 0..64),
            SparseRow::new(),
            "ecall-a7",
        );
    }
    // Slot-0 / instance-level rows tying S_in / S_out to the cycle fields.
    s2.push(
        one_form.clone(),
        add(&[
            h.px("S_in", 0, 0..32, |j| j, |j| ST_UPC + j),
            h.p("upc", 0, 0..32),
        ]),
        SparseRow::new(),
        "s-in-upc",
    );
    s2.push(
        one(cc.c("S_in", ST_JF, 0)),
        add(&[
            h.px("S_in", 0, 1..64, |j| j, |j| ST_JT + j),
            h.p("rpc", 0, 1..64),
        ]),
        SparseRow::new(),
        "s-in-jalr",
    );
    s2.push(
        one_form,
        add(&[
            h.px("S_out", 0, 0..64, |j| j, |j| ST_EX + j),
            h.px("S_in", 0, 0..64, |j| j, |j| ST_EX + j),
        ]),
        SparseRow::new(),
        "ex-carry",
    );
    Built { cols: cc, s1, s2 }
}

/// The B relation `s_1` (Python `build_s1`).
pub fn build_s1(params: &Params) -> Structure {
    build(params).s1
}

/// The K relation `s_2` (Python `build_s2`).
pub fn build_s2(params: &Params) -> Structure {
    build(params).s2
}

/// The public instance bound through the state segments
/// (Python's `public` dict).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PublicInputs {
    pub entry_upc: u32,
    pub exit_code: u64,
}

/// Public `init` (§6.6 (X2)): entry micro-PC, no pending JALR, not
/// halted, exit code (Python `init_vector`).
pub fn init_vector(public: &PublicInputs) -> Vec<bool> {
    let mut v = vec![false; 256];
    for i in 0..32 {
        v[ST_UPC + i] = (public.entry_upc >> i) & 1 == 1;
    }
    for i in 0..64 {
        v[ST_EX + i] = (public.exit_code >> i) & 1 == 1;
    }
    v
}

/// Public `fin` ((X3)): next micro-PC = `HALTED_UPC` (0), no pending
/// JALR, `halted = 1`, exit code (Python `fin_vector`).
pub fn fin_vector(public: &PublicInputs) -> Vec<bool> {
    let mut v = vec![false; 256];
    v[ST_HALT] = true;
    for i in 0..64 {
        v[ST_EX + i] = (public.exit_code >> i) & 1 == 1;
    }
    v
}

/// Witness size and constraint counts (Python `stats`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stats {
    pub cycles_per_instance: usize,
    pub nw: usize,
    pub used_bits: usize,
    pub direct_bits_per_cycle: usize,
    pub direct_bits_per_instance_state: usize,
    pub virtual_bits_per_cycle: usize,
    pub s1_rows: usize,
    pub s2_rows: usize,
    pub s1_rows_per_cycle: usize,
    pub s2_rows_per_cycle: usize,
    pub s1_nnz: usize,
    pub s2_nnz: usize,
}

/// Python `stats`.
pub fn stats(params: &Params) -> Stats {
    let b = build(params);
    let n = params.cycles();
    let direct = FIELDS
        .iter()
        .filter(|f| f.kind == Direct && !is_instance_field(f.name))
        .map(|f| f.width)
        .sum();
    let virt = FIELDS
        .iter()
        .filter(|f| f.kind == Virtual)
        .map(|f| f.width)
        .sum();
    let direct_inst = FIELDS
        .iter()
        .filter(|f| is_instance_field(f.name))
        .map(|f| f.width)
        .sum();
    Stats {
        cycles_per_instance: n,
        nw: b.cols.nw,
        used_bits: used_bits(params),
        direct_bits_per_cycle: direct,
        direct_bits_per_instance_state: direct_inst,
        virtual_bits_per_cycle: virt,
        s1_rows: b.s1.len(),
        s2_rows: b.s2.len(),
        s1_rows_per_cycle: b.s1.len() / n,
        s2_rows_per_cycle: b.s2.len() / n,
        s1_nnz: b.s1.nnz(),
        s2_nnz: b.s2.nnz(),
    }
}

// ---------------------------------------------------------------------------
// Witness generation
// ---------------------------------------------------------------------------

/// The ROM-owned witness fields of one row (Python `_rom_fields`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RomFields {
    pub imm: u64,
    pub kc: u64,
    pub rpc: u64,
    pub upc: u32,
    pub seq: u32,
    pub tgt: u32,
    /// Packed flag word: bit [`flag_pos`] of each flag.
    pub rf: u64,
    pub q_lo: u64,
    pub q_hi: u8,
    pub st_w: u8,
}

impl RomFields {
    /// The field named `name` as an integer, if it is a ROM field.
    /// Names match the witness segments: `imm kc rpc upc seq tgt rf
    /// Q_lo Q_hi st_w`.
    pub fn get(&self, name: &str) -> Option<u128> {
        Some(u128::from(match name {
            "imm" => self.imm,
            "kc" => self.kc,
            "rpc" => self.rpc,
            "upc" => u64::from(self.upc),
            "seq" => u64::from(self.seq),
            "tgt" => u64::from(self.tgt),
            "rf" => self.rf,
            "Q_lo" => self.q_lo,
            "Q_hi" => u64::from(self.q_hi),
            "st_w" => u64::from(self.st_w),
            _ => return None,
        }))
    }

    /// All ten `(name, value)` pairs, in Python dict order.
    pub fn entries(&self) -> [(&'static str, u128); 10] {
        [
            ("imm", u128::from(self.imm)),
            ("kc", u128::from(self.kc)),
            ("rpc", u128::from(self.rpc)),
            ("upc", u128::from(self.upc)),
            ("seq", u128::from(self.seq)),
            ("tgt", u128::from(self.tgt)),
            ("rf", u128::from(self.rf)),
            ("Q_lo", u128::from(self.q_lo)),
            ("Q_hi", u128::from(self.q_hi)),
            ("st_w", u128::from(self.st_w)),
        ]
    }
}

/// Python `_rom_fields`: pack a ROM row into its witness fields.
pub fn rom_fields(row: &Row) -> RomFields {
    let mut rf = 0u64;
    for &nm in &FLAG_NAMES {
        if row.flag(nm).expect("flag name") {
            rf |= 1u64 << fp(nm);
        }
    }
    for k in 0..6 {
        rf |= u64::from((row.bsel >> k) & 1) << fp(&format!("bsel{k}"));
    }
    for k in 0..8 {
        rf |= u64::from((row.ln >> k) & 1) << fp(&format!("ln{k}"));
        rf |= u64::from((row.fill >> k) & 1) << fp(&format!("fill{k}"));
    }
    RomFields {
        imm: row.imm,
        kc: row.kc,
        rpc: row.rpc,
        upc: row.upc,
        seq: row.seq,
        tgt: row.tgt,
        rf,
        q_lo: row.q_lo,
        q_hi: row.q_hi,
        st_w: row.st_w,
    }
}

/// All named field values of one cycle (Python `cycle_fields`): bit
/// `i` of each integer is bit `i` of the field. `dw` holds bits
/// 32..63 of the datapath `Dw` (Python `Dw >> 32`); `stc` is
/// `[old RAM word | store source]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CycleFields {
    pub v1: u64,
    pub v2: u64,
    pub rdv: u64,
    pub rw: u64,
    pub ridx: u64,
    pub y: u64,
    pub bop: u64,
    pub cin: u64,
    pub nw: u64,
    pub and_val: u64,
    /// Bits 32..63 of `dp.dw`, as a 32-bit field.
    pub dw: u32,
    pub t0: u64,
    pub t1: u64,
    pub t2: u64,
    pub gs: u64,
    pub shsrc: u64,
    pub stc: u128,
    pub off: u8,
    pub x1: u64,
    pub x2: u64,
    pub x3: u64,
    pub m: u64,
    pub l: u64,
    /// Packed single-bit witnesses: bit [`fl_pos`] of each.
    pub fl: u16,
    pub dynu: u32,
    pub rom: RomFields,
}

impl CycleFields {
    /// The field named `name` as an integer (witness segment names;
    /// `AND`, `Dw`, `Y`, `L` keep Python's casing), if it is a
    /// per-cycle field.
    pub fn get(&self, name: &str) -> Option<u128> {
        Some(match name {
            "v1" => u128::from(self.v1),
            "v2" => u128::from(self.v2),
            "rdv" => u128::from(self.rdv),
            "rw" => u128::from(self.rw),
            "ridx" => u128::from(self.ridx),
            "Y" => u128::from(self.y),
            "Bop" => u128::from(self.bop),
            "cin" => u128::from(self.cin),
            "nw" => u128::from(self.nw),
            "AND" => u128::from(self.and_val),
            "Dw" => u128::from(self.dw),
            "T0" => u128::from(self.t0),
            "T1" => u128::from(self.t1),
            "T2" => u128::from(self.t2),
            "Gs" => u128::from(self.gs),
            "shsrc" => u128::from(self.shsrc),
            "stc" => self.stc,
            "off" => u128::from(self.off),
            "x1" => u128::from(self.x1),
            "x2" => u128::from(self.x2),
            "x3" => u128::from(self.x3),
            "m" => u128::from(self.m),
            "L" => u128::from(self.l),
            "fl" => u128::from(self.fl),
            "dynu" => u128::from(self.dynu),
            other => return self.rom.get(other),
        })
    }

    /// All 35 per-cycle `(name, value)` pairs, in Python dict order
    /// (datapath fields, then ROM fields).
    pub fn entries(&self) -> Vec<(&'static str, u128)> {
        let mut out: Vec<(&'static str, u128)> = vec![
            ("v1", u128::from(self.v1)),
            ("v2", u128::from(self.v2)),
            ("rdv", u128::from(self.rdv)),
            ("rw", u128::from(self.rw)),
            ("ridx", u128::from(self.ridx)),
            ("Y", u128::from(self.y)),
            ("Bop", u128::from(self.bop)),
            ("cin", u128::from(self.cin)),
            ("nw", u128::from(self.nw)),
            ("AND", u128::from(self.and_val)),
            ("Dw", u128::from(self.dw)),
            ("T0", u128::from(self.t0)),
            ("T1", u128::from(self.t1)),
            ("T2", u128::from(self.t2)),
            ("Gs", u128::from(self.gs)),
            ("shsrc", u128::from(self.shsrc)),
            ("stc", self.stc),
            ("off", u128::from(self.off)),
            ("x1", u128::from(self.x1)),
            ("x2", u128::from(self.x2)),
            ("x3", u128::from(self.x3)),
            ("m", u128::from(self.m)),
            ("L", u128::from(self.l)),
            ("fl", u128::from(self.fl)),
            ("dynu", u128::from(self.dynu)),
        ];
        out.extend(self.rom.entries());
        out
    }
}

/// Python `cycle_fields`.
pub fn cycle_fields(rec: &TraceRecord) -> CycleFields {
    let d = &rec.dp;
    let mut fl = 0u16;
    let bit = |b: bool, pos: usize| -> u16 { u16::from(b) << pos };
    fl |= bit(d.cout, flp("cout"));
    fl |= bit(d.cond, flp("cond"));
    for k in 0..6 {
        fl |= bit(d.p[k], flp(&format!("p{k}")));
    }
    fl |= bit(d.u1, flp("u1"));
    fl |= bit(d.u2, flp("u2"));
    fl |= (d.rdslt as u16) << flp("rdslt");
    fl |= (d.eqres as u16) << flp("eqres");
    fl |= bit(d.take, flp("take"));
    fl |= bit(d.tb, flp("tb"));
    fl |= bit(d.th, flp("th"));
    fl |= bit(d.tw, flp("tw"));
    CycleFields {
        v1: rec.v1,
        v2: rec.v2,
        rdv: rec.rd_val,
        rw: rec.ram_old,
        ridx: rec.ram_idx as u64,
        y: d.y,
        bop: d.bop,
        cin: d.cin,
        nw: d.nw,
        and_val: d.and_val,
        dw: (d.dw >> 32) as u32,
        t0: d.t0,
        t1: d.t1,
        t2: d.t2,
        gs: d.gs,
        shsrc: rec.v1,
        stc: u128::from(rec.ram_old) | (u128::from(rec.v2) << 64),
        off: d.off,
        x1: d.x1,
        x2: d.x2,
        x3: d.x3,
        m: d.m,
        l: d.l,
        fl,
        dynu: rec.dynu,
        rom: rom_fields(&rec.rom),
    }
}

/// State after cycle `k`: next micro-PC, pending-JALR target, halted
/// flag of cycle `k`, exit code (Python `_state_out`).
fn state_out(trace: &[TraceRecord], k: usize, exit_code: u64) -> Vec<bool> {
    let rec = &trace[k];
    let row = &rec.rom;
    let mut v = vec![false; 256];
    for i in 0..32 {
        v[ST_UPC + i] = (rec.next_upc >> i) & 1 == 1;
    }
    if row.jalr {
        let tgt = rec.dp.s & !1 & M64;
        for j in 1..64 {
            v[ST_JT + j] = (tgt >> j) & 1 == 1;
        }
        v[ST_JF] = true;
    }
    v[ST_HALT] = row.halted;
    for i in 0..64 {
        v[ST_EX + i] = (exit_code >> i) & 1 == 1;
    }
    v
}

/// State before cycle `k` (`k` = first cycle of an instance): the
/// out-state of cycle `k-1`, or init (Python `_state_in`).
fn state_in(trace: &[TraceRecord], k: usize, exit_code: u64) -> Vec<bool> {
    if k == 0 {
        let mut v = vec![false; 256];
        for i in 0..32 {
            v[ST_UPC + i] = (trace[0].upc >> i) & 1 == 1;
        }
        for i in 0..64 {
            v[ST_EX + i] = (exit_code >> i) & 1 == 1;
        }
        return v;
    }
    state_out(trace, k - 1, exit_code)
}

/// `W`: one row (list of `NW` bits) per SIMD instance (Python
/// `witness`). `exit_code` defaults to the value of `a0` read by the
/// final (`HALTED`) cycle.
///
/// # Panics
/// If the trace is empty or its length is not a multiple of
/// `2^log_cycles` (Python `assert`).
pub fn witness(trace: &[TraceRecord], params: &Params, exit_code: Option<u64>) -> Vec<Vec<bool>> {
    witness_packed(trace, params, exit_code)
        .iter()
        .map(|row| row.to_bools())
        .collect()
}

/// [`witness`] with rows in packed form ([`PackedBits`], one bit per
/// witness bit instead of one byte). The bits are identical; the
/// prover consumes this form so a large trace's witness is never
/// expanded.
pub fn witness_packed(
    trace: &[TraceRecord],
    params: &Params,
    exit_code: Option<u64>,
) -> Vec<PackedBits> {
    let cc = Cols::new(params);
    let n = params.cycles();
    let exit_code = exit_code.unwrap_or_else(|| trace.last().map_or(0, |r| r.v1));
    assert!(
        !trace.is_empty() && trace.len().is_multiple_of(n),
        "trace length must be a nonzero multiple of 2^c"
    );
    // Instances are independent; build them in parallel (order kept).
    (0..trace.len() / n)
        .into_par_iter()
        .map(|j| {
            let mut w = PackedBits::zero(cc.nw);
            for t in 0..n {
                for (name, val) in cycle_fields(&trace[j * n + t]).entries() {
                    let width = field(name).expect("field name").width;
                    let base = cc.c(name, 0, t);
                    for i in 0..width {
                        if (val >> i) & 1 == 1 {
                            w.set(base + i);
                        }
                    }
                }
            }
            for (name, st) in [
                ("S_in", state_in(trace, j * n, exit_code)),
                ("S_out", state_out(trace, j * n + n - 1, exit_code)),
            ] {
                for (i, &v) in st.iter().enumerate() {
                    if v {
                        w.set(cc.c(name, i, 0));
                    }
                }
            }
            w
        })
        .collect()
}

/// Python `public_inputs`.
pub fn public_inputs(program: &Program, exit_code: u64) -> PublicInputs {
    PublicInputs {
        entry_upc: program.entry_upc,
        exit_code: exit_code & M64,
    }
}

// ---------------------------------------------------------------------------
// Checker
// ---------------------------------------------------------------------------

/// XOR of the coefficients selected by the bit vector `z`
/// (Python `_dot`).
fn dot(row: &SparseRow, z: &[bool]) -> K {
    let mut acc = K::ZERO;
    for (&c, &v) in row {
        if z[c] {
            acc += v;
        }
    }
    acc
}

/// The violated constraints of `w` (empty means accepted): both
/// relations evaluated directly on every instance, plus (X1)–(X3) of
/// spec 06 §6.6 and, if `program` is given, that the ROM-owned
/// virtual segments equal the ROM row at the claimed micro-PC
/// (Python `violations`).
///
/// # Panics
/// If `w` is empty or a row is shorter than a referenced column
/// (Python raises `IndexError`).
pub fn violations(
    w: &[Vec<bool>],
    public: &PublicInputs,
    params: &Params,
    program: Option<&Program>,
) -> Vec<String> {
    let b = build(params);
    let cc = &b.cols;
    let nw = cc.nw;
    let q = w.len();
    let mut out: Vec<String> = Vec::new();
    let zs: Vec<Vec<bool>> = (0..q)
        .map(|j| {
            let mut z = w[j].clone();
            z.push(true);
            z.resize(2 * nw, false);
            z
        })
        .collect();
    for (j, z) in zs.iter().enumerate() {
        for r in 0..b.s1.len() {
            let (a, bb, c) = (dot(&b.s1.a[r], z), dot(&b.s1.b[r], z), dot(&b.s1.c[r], z));
            if a.value() & bb.value() != c.value() {
                out.push(format!("s1[{j}] row {r} ({})", b.s1.tags[r]));
            }
        }
        for r in 0..b.s2.len() {
            let (a, bb, c) = (dot(&b.s2.a[r], z), dot(&b.s2.b[r], z), dot(&b.s2.c[r], z));
            if a * bb != c {
                out.push(format!("s2[{j}] row {r} ({})", b.s2.tags[r]));
            }
        }
    }
    let st =
        |j: usize, name: &str| -> Vec<bool> { (0..256).map(|i| w[j][cc.c(name, i, 0)]).collect() };
    for j in 1..q {
        if st(j, "S_in") != st(j - 1, "S_out") {
            out.push(format!("X1[{j}]: S_in != previous S_out"));
        }
    }
    if st(0, "S_in") != init_vector(public) {
        out.push("X2: S_in(0) != init".to_string());
    }
    if st(q - 1, "S_out") != fin_vector(public) {
        out.push("X3: S_out(q-1) != fin".to_string());
    }
    if let Some(program) = program {
        let n = params.cycles();
        for (j, _) in w.iter().enumerate() {
            for t in 0..n {
                let get = |name: &str| -> u128 {
                    let width = field(name).expect("field name").width;
                    (0..width)
                        .map(|i| u128::from(w[j][cc.c(name, i, t)]) << i)
                        .fold(0, |acc, x| acc | x)
                };
                let upc = get("upc") as usize;
                if upc >= program.rom.len() {
                    out.push(format!("rom[{j},{t}]: upc out of range"));
                    continue;
                }
                let want = rom_fields(&program.rom[upc]);
                for (name, val) in want.entries() {
                    if get(name) != val {
                        out.push(format!("rom[{j},{t}] {name}"));
                    }
                }
            }
        }
    }
    out
}

/// Whether `w` is accepted (Python `check`).
pub fn check(
    w: &[Vec<bool>],
    public: &PublicInputs,
    params: &Params,
    program: Option<&Program>,
) -> bool {
    violations(w, public, params, program).is_empty()
}
