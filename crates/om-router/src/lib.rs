//! BinaryRouter for Open Magnetar: the shift and sub-word store routing
//! instances.
//!
//! Normative reference: `docs/spec/08-router.md` (with CONVENTIONS C2, C5,
//! C7). Behavioral reference: `reference/openmagnetar/router.py`, whose
//! public surface this crate mirrors in [`router`]: the routing supports
//! (`shift_entries`, `store_entries`), the independent integer semantics
//! (`apply_shift`, `apply_store`), the verifier routing-matrix evaluations
//! (`shift_r_eval`, `store_r_eval`), the witness builders
//! (`shift_witness`, `store_witness`), and the dense and fast
//! prove/verify pairs.
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python `shift_R_eval`/`store_R_eval` are [`router::shift_r_eval`] /
//!   [`router::store_r_eval`] (snake_case).
//! - The Python witness dicts are the structs [`router::ShiftWitness`]
//!   (keys `X`, `Qlo`, `Qhi`, `Y`) and [`router::StoreWitness`] (keys
//!   `X`, `Q`, `abits`, `Inc`), with public fields so callers can replace
//!   e.g. `abits` exactly as `protocol.py` does. Bit tables are
//!   `Vec<bool>` (Python `list[int]` of 0/1); words are `u64` and
//!   indices `usize`.
//! - A cycle's optional routing keeps Python's tuple order: shifts carry
//!   `(amt, kind)`, stores carry `(width, offset)`.
//! - Python `VerificationError` is returned as `Err` from every
//!   `*_verify`; Python `ValueError` programmer errors (a bad shift kind
//!   in `shift_source`, a sum-check claim inconsistent with the prover's
//!   own tables) **panic**, matching `om-sumcheck`/`om-memcheck`.
//! - Output claims are [`om_memcheck::onehot::EvalClaim`]s, exactly as
//!   Python's `router.py` emits `onehot.EvalClaim`s; this crate depends
//!   on `om-memcheck` for that canonical type.

pub mod router;

pub use router::{
    DIRECT_ROUNDS, KIND_NAMES, NO_ROUTE, RouterProof, SEXT32, SLL, SLLW, SRA, SRAW, SRL, SRLW,
    ShiftCompact, ShiftCycle, ShiftWitness, StoreCompact, StoreCycle, StoreWitness, ZEXT32,
    apply_shift, apply_store, shift_entries, shift_prove, shift_prove_compact,
    shift_prove_compact_with, shift_prove_fast, shift_r_eval, shift_source, shift_valid,
    shift_verify, shift_witness, store_entries, store_prove, store_prove_compact,
    store_prove_compact_with, store_prove_fast, store_r_eval, store_valid, store_verify,
    store_witness,
};

/// Concatenate a transcript label suffix, as Python's `label + b"/…"`.
pub(crate) fn sublabel(label: &[u8], suffix: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(label.len() + suffix.len());
    out.extend_from_slice(label);
    out.extend_from_slice(suffix);
    out
}
