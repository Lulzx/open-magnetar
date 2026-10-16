//! Multilinear extensions and sum-check for Open Magnetar.
//!
//! Normative reference: `docs/spec/03-sumcheck.md` (with CONVENTIONS C2/C3).
//! Behavioral reference: `reference/openmagnetar/mle.py` and
//! `reference/openmagnetar/sumcheck.py`, whose public surface (C8) this
//! crate mirrors: [`eq_table`], [`eq_eval`], [`mle_eval`], [`bind_low`],
//! [`SumcheckProof`], [`sumcheck_prove`], [`sumcheck_verify`],
//! [`VerificationError`], plus [`interpolate_eval`], [`batch_claims`], and
//! [`batched_combine`].
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python `ValueError`s (programmer errors: `degree < 1`, malformed
//!   tables, >256 batched claims, …) **panic**; `VerificationError` is
//!   returned as `Err` from [`sumcheck_verify`]. This matches the mapping
//!   already used by `om-transcript`.
//! - Python's `mle_eval` accepts bit tables (`0`/`1` ints); Rust provides
//!   [`mle_eval_bits`] over `&[bool]` alongside [`mle_eval`] over `&[K]`.
//!   Bit tables passed to [`sumcheck_prove`] must be converted with
//!   `K::from_bit` by the caller.
//! - [`sumcheck_prove`] takes the tables by value (`Vec<Vec<K>>`) because
//!   it binds them in place round by round.
//! - Python's private `sumcheck._init` is exported as [`sumcheck_init`]
//!   because `router.py` calls it directly.
//!
//! Univariate skip (spec 03 §3.9) is OFF in the v1 wire protocol
//! (`sumcheck_version = 1`), and is provided via [`UnivariateSkipProof`],
//! [`lagrange_subspace_weights`], [`bind_low_subspace`], [`sumcheck_prove_skip`],
//! and [`sumcheck_verify_skip`] for `sumcheck_version = 2` callers.

pub mod mle;
pub mod sumcheck;

pub use mle::{
    PackedBits, bind_low, bind_low_in_place, eq_eval, eq_table, mle_eval, mle_eval_bits,
    mle_eval_packed,
};
pub use sumcheck::{
    BoxedCombine, MAX_BATCH_CLAIMS, SumcheckProof, UnivariateSkipProof, VerificationError,
    batch_claims, batched_combine, bind_low_subspace, combine_sum, interpolate_eval,
    lagrange_subspace_weights, sumcheck_init, sumcheck_prove, sumcheck_prove_rounds,
    sumcheck_prove_skip, sumcheck_round_evals, sumcheck_round_evals_mul2, sumcheck_verify,
    sumcheck_verify_skip,
};
