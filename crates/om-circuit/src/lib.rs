//! The CPU circuit for Open Magnetar: witness layout, the two R1CS
//! relations `s_1` (over `B`) and `s_2` (over `K`), witness generation
//! from an execution trace, and the standalone checker.
//!
//! Normative reference: `docs/spec/10-cpu-circuit.md` (with CONVENTIONS
//! C2 — the witness-matrix exception — C5, C7). Behavioral reference:
//! `reference/openmagnetar/cpu_circuit.py`, whose public surface this
//! crate mirrors in the module [`circuit`].
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python assert failures (bad parameters, malformed trace/witness)
//!   **panic**, matching the other `om-*` crates.
//! - Witness rows `W` are `Vec<Vec<bool>>` (Python's `list[list[int]]` of
//!   0/1); the public-instance dict is [`circuit::PublicInputs`].
//! - Sparse rows are `BTreeMap<usize, K>` (column → coefficient) rather
//!   than dicts of plain ints; every Python coefficient is the integer
//!   value of a `K` element (C1), and [`circuit::Structure::to_r1cs`]
//!   performs the conversion `keygen.py` does.
//! - Segment `kind` reuses [`om_spartan::SegmentKind`]; the string
//!   owner is [`circuit::Owner`]. `FLAG_POS`/`FL_POS` are the lookup
//!   functions [`circuit::flag_pos`] / [`circuit::fl_pos`].
//! - Trace records and ROM rows are `om_isa` types (its `bytecode`
//!   module mirrors the `bytecode.py` dicts `cpu_circuit.py` consumes);
//!   the datapath intermediates come from the records, not recomputed.

pub mod circuit;

pub use circuit::{
    Built, Cols, CycleFields, FIELDS, FL_NAMES, FieldDef, INSTANCE_FIELDS, Owner, Params,
    PublicInputs, RomFields, Segment, SparseRow, Stats, Structure, build, build_s1, build_s2,
    check, cycle_fields, field, fin_vector, fl_pos, flag_pos, init_vector, is_instance_field,
    layout, num_w_cols, public_inputs, relations, rom_fields, segment, stats, used_bits,
    violations, witness,
};
