//! SIMD R1CS, BinarySpartan and Virtual Spartan for Open Magnetar.
//!
//! Normative reference: `docs/spec/06-spartan.md` (with CONVENTIONS
//! C2 — including the witness-matrix exception — C3, C8). Behavioral
//! reference: `reference/openmagnetar/r1cs.py` and
//! `reference/openmagnetar/spartan.py`, whose public surface this crate
//! mirrors in the modules [`r1cs`] and [`spartan`].
//!
//! Judgment calls where Rust idiom differs from the Python model (see
//! the module docs for details):
//!
//! - Python `ValueError`s (programmer errors) **panic**;
//!   `VerificationError` is returned as `Err` from [`spartan::verify`],
//!   matching the mapping already used by `om-transcript` and
//!   `om-sumcheck`.
//! - Bit vectors are `&[bool]` (Python `list[int]` of 0/1); the witness
//!   `W` is `&[Vec<bool>]` and the public inputs `X` are `&[Vec<K>]`.
//!   The cross-step boundary states `init`/`fin` are `Vec<bool>`
//!   (spec 06 §6.6 has them in `B^(2^lam)`).
//! - The string tags of Python (`field: "B"/"K"`, segment
//!   `kind: "direct"/"virtual"/"pad"`) are the enums
//!   [`r1cs::RelationField`] and [`spartan::SegmentKind`].
//! - [`spartan::Claim`] is `om_mosaic::Claim` (Python's `spartan.py`
//!   imports `Claim` from `mosaic.py`), re-exported here; ids are
//!   `i64` because the no-layout whole-`W` claim uses Python's
//!   `comp_id=-1` sentinel.

pub mod r1cs;
pub mod spartan;

pub use r1cs::{
    R1CS, RelationField, SparseMatrix, build_z, check_witness_bits, flatten_w, public_part,
    simd_satisfied,
};
pub use spartan::{
    Claim, CrossStep, Segment, SegmentKind, SpartanProof, check_layout, next_mle, prove,
    segment_table, verify, xs_weights,
};
