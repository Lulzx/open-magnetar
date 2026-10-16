//! BinaryTwist and BinaryShout memory checking for Open Magnetar.
//!
//! Normative reference: `docs/spec/07-twist-shout.md` (with CONVENTIONS
//! C2, C5, C6). Behavioral reference:
//! `reference/openmagnetar/onehot.py`, `shout.py` and `twist.py`, whose
//! public surface this crate mirrors module by module: [`onehot`]
//! (address decomposition, the `Δ⋆` Frobenius one-hot check, address
//! virtualization), [`shout`] (BinaryShout) and [`twist`]
//! (BinaryTwist, `LT`, final memory, Inc-at-a-random-point).
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Bit tables (`ra`, `M_0`) are `Vec<bool>` (Python `list[int]` of
//!   0/1); words are `u64` and addresses `usize`. The prover's address
//!   components are [`onehot::AddrComps`] (one address per cycle, or
//!   arbitrary bit tables for cheating-prover tests) and its `Inc`
//!   table is one `u64` word per cycle (spec 07 §7.10): no prover
//!   phase holds a `2^ac · T` or `2^ell · T` table of bools or field
//!   elements.
//! - Python `VerificationError` is returned as `Err` from every
//!   `*_verify`; Python `assert`/`ValueError` programmer errors
//!   (e.g. `d ∤ a` in [`onehot::comp_tables`]) **panic**, matching
//!   `om-transcript`/`om-sumcheck`/`om-mosaic`.
//! - Output claims are [`onehot::EvalClaim`]s — `(poly, point, value)`
//!   with a polynomial *name* — exactly as Python's `onehot.py`,
//!   `shout.py` and `twist.py` emit them and as spec 07 §7.1 defines a
//!   claim. Python's `protocol.py` converts them to `mosaic.Claim`
//!   (`comp_id`, point, value) via its name→id map
//!   (`_to_mosaic`); [`onehot::EvalClaim::to_mosaic_claim`] is that
//!   conversion. This crate therefore depends on `om-mosaic` only for
//!   that canonical target type.
//! - [`twist::build_witness`]'s Python `info` dict is the struct
//!   [`twist::TwistInfo`] (its `"final"` key is `final_state`).
//! - `twist_verify`'s Python callable `m0_eval` is
//!   `&dyn Fn(&[K]) -> K`.
//! - Python keyword arguments `final=`/`inc_extra=` are the trailing
//!   positional parameters `final_mem: Option<&FinalMem>` and
//!   `inc_extra_flag: bool`.

mod lazy;
pub mod onehot;
pub mod shout;
pub mod twist;

/// Concatenate a transcript label suffix, as Python's
/// `label + b"/…"`.
pub(crate) fn sublabel(label: &[u8], suffix: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(label.len() + suffix.len());
    out.extend_from_slice(label);
    out.extend_from_slice(suffix);
    out
}
