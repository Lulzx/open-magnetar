//! MosaicPCS layout, lifting and batching sum-check for Open Magnetar.
//!
//! Normative reference: `docs/spec/05-mosaic.md` (with CONVENTIONS C2).
//! Behavioral reference: `reference/openmagnetar/mosaic.py`, whose public
//! surface this crate mirrors: [`Claim`], [`Placement`], [`Layout`],
//! [`compute_layout`], [`build_g`], [`lift_point`], [`eq_sum_table`],
//! [`BatchProof`], [`batch_prove`], [`batch_verify`], [`direct_g_eval`],
//! [`LABEL`], [`MAX_CLAIMS`].
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python `ValueError`s (programmer errors: empty/duplicate/bad
//!   components, malformed tables, >256 claims in the prover, a false
//!   claim handed to the prover) **panic**; `VerificationError` is
//!   returned as `Err` from [`lift_point`] and [`batch_verify`],
//!   matching the mapping already used by `om-transcript`,
//!   `om-sumcheck` and `om-spartan`.
//! - Bit tables and `G` are `bool` vectors (Python `list[int]` of 0/1),
//!   [`build_g`] takes them as a [`BTreeMap`] keyed by component id
//!   (Python dict; a missing entry panics, as Python's `KeyError`).
//!   [`build_g_packed`] and [`batch_prove_packed`] are the same
//!   operations over packed bit tables, for provers that must not
//!   expand `G` to a byte (or a field element) per bit.
//! - [`Claim::comp_id`] is `i64`, not `u32`: Python's `spartan.py`
//!   emits a whole-witness claim with the sentinel `comp_id = -1` in
//!   its no-layout mode, and this crate owns the canonical `Claim`
//!   type (Python `mosaic.Claim`). Genuine components keep spec 05
//!   §5.1's `id ∈ [0, 2^32)`: [`compute_layout`] rejects anything
//!   outside that range, so `-1` can never name a component and
//!   [`lift_point`] rejects it as unknown.
//! - The Python module has a single file, so this crate puts
//!   everything at the root (no `mosaic` submodule).

pub mod mosaic;

pub use mosaic::{
    BIT_ROUNDS, BatchProof, Claim, LABEL, Layout, MAX_CLAIMS, Placement, batch_prove,
    batch_prove_packed, batch_prove_packed_with, batch_verify, build_g, build_g_packed,
    compute_layout, direct_g_eval, eq_sum_table, lift_point,
};
