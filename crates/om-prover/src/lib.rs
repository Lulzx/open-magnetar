//! The Open Magnetar prover: KeyGen, execution and proving
//! (Construction 3, prover side).
//!
//! Normative reference: `docs/spec/11-protocol.md` (§11.2 KeyGen,
//! §11.3–§11.5, §11.7 claim graph) with `12-proof-format.md` for the
//! encodings. Behavioral reference: `reference/openmagnetar/keygen.py`
//! (in [`keygen`]), `params.py` (in [`params`], the §13.2 soundness
//! ledger and proof-size model) and the prover side of
//! `protocol.py` (in [`prove`], with the prover/verifier-shared
//! helpers in [`common`] for `om-verifier` to reuse).
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - The `VerifyingKey` type is `om_format::VerifyingKey`. Python's
//!   `VerifyingKey` additionally carries two *behavioral* members
//!   with no wire fields: the cached property `derived` and the
//!   cached `hasher`/`digest()`. `om-format` provides `hasher()` and
//!   `digest()` computing on demand, but has no `derived` cache
//!   (deliberately: derivation is this crate's job), so callers build
//!   a [`keygen::Derived`] explicitly. No wire field is missing.
//! - Python `KeyError_` is [`keygen::KeyError`]; prover failures are
//!   [`prove::ProverError`]. Sub-crate asserts (programmer errors)
//!   still panic, matching the other `om-*` crates.
//! - Python's test-only `hooks={"trace": fn}` is
//!   [`prove::prove_instance_with_trace_hook`] / the `hook` argument
//!   of [`prove::prove_execution`].

pub mod common;
pub mod keygen;
pub mod params;
pub mod prove;

pub use keygen::{
    Derived, Instance, KeyError, LOG_CYCLES, MAX_LOG_T, REG_A, REG_D, REG_P, VK_VERSION, WORD_BITS,
    keygen, keygen_default, keygen_from_elf,
};
pub use prove::{
    DEFAULT_MAX_CYCLES, Execution, ProverError, TraceHook, execute, execute_with_derived, prove,
    prove_execution, prove_instance, prove_instance_with_trace_hook,
};
