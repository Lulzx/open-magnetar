//! Fiat-Shamir transcript and hash profiles for Open Magnetar.
//!
//! Normative reference: `docs/spec/02-transcript.md` (with CONVENTIONS C4).
//! Behavioral reference: `reference/openmagnetar/hashing.py` and
//! `reference/openmagnetar/transcript.py`.
//!
//! Hash profiles (`sha256` default, `sha3-256`, `sha384`) are implemented
//! from scratch in this crate — no external hash crates, per project rule.
//! The transcript is a hash chain: state `S` plus a squeeze counter reset
//! by every absorb; domain bytes `0x00`/`0x01`/`0x02` separate init,
//! absorb, and squeeze; labels and data are length-prefixed via [`enc`].
//!
//! Judgment calls where Rust idiom differs from the Python model:
//! invalid labels (spec 02 §2.7) and `challenge_index` with `bits > 64`
//! **panic** with a clear message, where Python raises `ValueError`;
//! an unknown hash profile is rejected by [`Hasher::from_profile_id`]
//! returning `None`.

mod hashing;
mod keccak;
mod sha256;
mod sha512;
mod transcript;

pub use hashing::Hasher;
pub use transcript::{
    DOM_ABSORB, DOM_INIT, DOM_SQUEEZE, Transcript, VERSION_LABEL, enc, is_valid_label, u64le,
};
