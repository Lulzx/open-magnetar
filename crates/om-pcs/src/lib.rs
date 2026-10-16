//! Polynomial commitment for Open Magnetar: Merkle trees, the additive-NTT
//! Reed–Solomon code, Ligerito, ring switching, and the PCS trait.
//!
//! Normative reference: `docs/spec/04-pcs.md` (with CONVENTIONS C1–C4, C8).
//! Behavioral reference: `reference/openmagnetar/{merkle,ntt,ligerito,
//! ring_switch,pcs}.py`, whose module split and public surface this crate
//! mirrors.
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python `ValueError`s (programmer errors: bad parameters, wrong table
//!   or point length, unknown profile, …) **panic**; `VerificationError`
//!   is returned as `Err` from verifiers, matching `om-sumcheck` /
//!   `om-transcript`.
//! - Merkle digests are `Vec<u8>` ([`merkle::Digest`]), since the sha384
//!   profile outputs 48 bytes (Python `bytes`).
//! - Python takes tables/states by reference and never mutates them; Rust
//!   does the same (`&[K]`, `&LevelData`), except
//!   [`ligerito::commit_level`], which takes its table by value because it
//!   stores it in the [`ligerito::LevelData`] it returns.
//! - `LigeritoProof.final` is named `final_poly` in Rust.
//! - Bit vectors are `&[bool]` (Python `list[int]` of 0/1).
//! - `soundness_bits` returns [`ligerito::SoundnessBits`] structs instead
//!   of Python dicts; `make_params(n, profile, r)` has no defaulted
//!   arguments. Python `ligerito.make_params` has no `"test"` profile
//!   (that profile is assembled in `keygen.py`, out of scope here), so
//!   neither does this crate.

pub mod ligerito;
pub mod merkle;
pub mod ntt;
pub mod pcs;
pub mod ring_switch;

pub use ligerito::{LevelData, LevelOpening, LigeritoParams, LigeritoProof};
pub use pcs::{BitPCS, BitProof, BitState, BitStatePacked, Commitment, LigeritoPCS, Pcs};
pub use ring_switch::RingSwitchProof;
