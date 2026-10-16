//! The Open Magnetar verifier (spec §11.6, Construction 3 verifier
//! side).
//!
//! Normative reference: `docs/spec/11-protocol.md` (§11.3 statement
//! checks, §11.6 verifier, §11.7 claim graph, §11.8 transcript order)
//! and `docs/spec/13-security.md` §13.8 (verifier DoS/bounds duties).
//! Behavioral reference: `reference/openmagnetar/protocol.py`
//! (`verify`, `verify_strict` and the helpers they share with the
//! prover).
//!
//! The prover/verifier-shared composition helpers (statement and
//! commitment absorption, `M̃_0`, the bytecode Shout plan, Mosaic
//! claim assembly, segment-claim splitting) are reused unchanged
//! from `om_prover::common`; key derivation is `om_prover::Derived`.
//! This crate adds only the verifier's own sequence of checks, in
//! §11.6 order.
//!
//! Semantics mirror Python exactly: [`verify`] is the bool form
//! ("any malformed or inconsistent input is a rejection", never
//! panics on attacker-controlled input) and accepts both an
//! in-memory [`Proof`] and an encoded blob through [`ProofRef`],
//! like Python's `isinstance(proof, (bytes, bytearray))` dispatch.
//! [`verify_strict`] is the raising form, returning
//! [`VerificationError`] (the error type every sub-verifier uses);
//! decoders and derivation failures are mapped onto it, since Python
//! catches every exception in `verify` alike.
//!
//! Bounds (§13.8) enforced before allocating on attacker input:
//! blob length (`om_format::MAX_BYTES`, defined but unused in
//! Python — enforced here via `decode_proof`'s reader and an
//! explicit pre-check); `T` a power of two in `[4, 2^40]`
//! (`Derived::instance`); the vk validated (`VerifyingKey::validate`,
//! which bounds `A <= 40`, the I/O window, `MAX_CODE` and recomputes
//! `program_digest`), plus the CPU circuit's `3 <= A <= 28` checked
//! before `Derived::new` can assert on it; Ligerito `t`/`k`/`gs`
//! taken only from the vk-derived parameters (the proof carries
//! none); `proof.log_t`, root length and PCS-variant consistency
//! with the vk; canonical output / fitting input via
//! `encode_region` / `build_m0`; the `2^s` public-input vector
//! allocated fallibly. Python's `0 <= exit_code < 2^64` check is a
//! tautology for Rust's `u64` and is therefore not repeated.

use std::panic::{AssertUnwindSafe, catch_unwind};

use om_circuit::circuit as cpu;
use om_elf::encode_region;
use om_field::K;
use om_format::{PcsMode, PcsProof, Proof, PublicInstance, VerifyingKey, decode_proof};
use om_memcheck::shout::shout_verify;
use om_memcheck::twist::{FinalMem, TwistClaims, twist_verify};
use om_mosaic::batch_verify;
use om_pcs::pcs::Commitment;
use om_pcs::ring_switch::rs_verify;
use om_prover::Derived;
use om_prover::common::{
    LABEL, ShoutPlan, absorb_commitment, absorb_statement, m0_eval, m0_words, mosaic_claims,
    ram_bits_ok, same_point, seg_claims, transparent_root,
};
use om_prover::keygen::{REG_A, WORD_BITS};
use om_router::{shift_verify, store_verify};
use om_spartan::spartan::CrossStep;
use om_sumcheck::mle_eval_bits;
use om_transcript::Transcript;

pub use om_sumcheck::VerificationError;

/// A proof in either accepted form (Python's type dispatch in
/// `verify`): an in-memory [`Proof`] or its canonical `OMPF` blob.
#[derive(Clone, Copy, Debug)]
pub enum ProofRef<'a> {
    /// The in-memory proof.
    Proof(&'a Proof),
    /// The encoded proof blob (decoded against `(vk, T)`).
    Bytes(&'a [u8]),
}

impl<'a> From<&'a Proof> for ProofRef<'a> {
    fn from(p: &'a Proof) -> ProofRef<'a> {
        ProofRef::Proof(p)
    }
}

impl<'a> From<&'a [u8]> for ProofRef<'a> {
    fn from(b: &'a [u8]) -> ProofRef<'a> {
        ProofRef::Bytes(b)
    }
}

impl<'a> From<&'a Vec<u8>> for ProofRef<'a> {
    fn from(b: &'a Vec<u8>) -> ProofRef<'a> {
        ProofRef::Bytes(b)
    }
}

/// Diagnostics of an accepted proof (for conformance tests; Python
/// counts the Mosaic claims by patching `batch_prove`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verified {
    /// Number of Mosaic claims assembled in §11.7 order (68 for the
    /// reference layout; `batch_verify` rejects more than 256).
    pub mosaic_claims: usize,
}

fn err<E: std::fmt::Display>(e: E) -> VerificationError {
    VerificationError::new(e.to_string())
}

/// Pre-derivation vk checks: validation and the CPU circuit's
/// `3 <= A <= 28` bound (Python raises there; `Derived::new` would
/// panic, so the bool entry points must check before deriving).
fn check_vk(vk: &VerifyingKey) -> Result<(), VerificationError> {
    vk.validate().map_err(err)?;
    if !(3..=28).contains(&vk.abi.ram_log_words) {
        return Err(VerificationError::new("A must satisfy 3 <= A <= 28"));
    }
    Ok(())
}

/// Accept or reject (Python `protocol.verify`). Any malformed or
/// inconsistent input — including a sub-verifier panicking on a
/// hand-built in-memory proof, as Python catches every exception —
/// is a rejection (`false`).
pub fn verify(vk: &VerifyingKey, instance: &PublicInstance, proof: ProofRef<'_>) -> bool {
    catch_unwind(AssertUnwindSafe(|| {
        let Ok(()) = check_vk(vk) else { return false };
        let derived = Derived::new(vk);
        verify_with_derived(&derived, instance, proof)
    }))
    .unwrap_or(false)
}

/// [`verify`] against a prebuilt [`Derived`] (Python caches
/// `vk.derived`; derivation is the expensive part for retries).
pub fn verify_with_derived(
    derived: &Derived,
    instance: &PublicInstance,
    proof: ProofRef<'_>,
) -> bool {
    catch_unwind(AssertUnwindSafe(|| match proof {
        ProofRef::Proof(p) => verify_strict_with_derived(derived, instance, p).is_ok(),
        ProofRef::Bytes(b) => verify_bytes_strict_with_derived(derived, instance, b).is_ok(),
    }))
    .unwrap_or(false)
}

/// The strict verifier on an in-memory proof (Python
/// `protocol.verify_strict`), deriving from `vk` internally; use
/// [`verify_strict_with_derived`] to reuse a [`Derived`].
///
/// # Errors
/// Returns [`VerificationError`] on any failing check of §11.6.
pub fn verify_strict(
    vk: &VerifyingKey,
    instance: &PublicInstance,
    proof: &Proof,
) -> Result<(), VerificationError> {
    check_vk(vk)?;
    verify_strict_with_derived(&Derived::new(vk), instance, proof)
}

/// The strict verifier on an encoded proof blob: decode against
/// `(vk, instance.T)`, then [`verify_strict`] (the blob arm of
/// Python `verify`).
///
/// # Errors
/// Returns [`VerificationError`] on a malformed blob or any failing
/// check of §11.6.
pub fn verify_bytes_strict(
    vk: &VerifyingKey,
    instance: &PublicInstance,
    blob: &[u8],
) -> Result<(), VerificationError> {
    check_vk(vk)?;
    verify_bytes_strict_with_derived(&Derived::new(vk), instance, blob)
}

/// [`verify_strict`] against a prebuilt [`Derived`].
///
/// # Errors
/// Returns [`VerificationError`] on any failing check of §11.6.
pub fn verify_strict_with_derived(
    derived: &Derived,
    instance: &PublicInstance,
    proof: &Proof,
) -> Result<(), VerificationError> {
    verify_detailed_with_derived(derived, instance, proof).map(|_| ())
}

/// [`verify_bytes_strict`] against a prebuilt [`Derived`].
///
/// # Errors
/// Returns [`VerificationError`] on a malformed blob or any failing
/// check of §11.6.
pub fn verify_bytes_strict_with_derived(
    derived: &Derived,
    instance: &PublicInstance,
    blob: &[u8],
) -> Result<(), VerificationError> {
    if blob.len() > om_format::MAX_BYTES {
        return Err(VerificationError::new("proof blob too large"));
    }
    let inst = derived.instance(instance.t).map_err(err)?;
    let shape = derived.proof_shape(&inst);
    let proof = decode_proof(&derived.vk, blob, instance.t, &shape).map_err(err)?;
    verify_detailed_with_derived(derived, instance, &proof).map(|_| ())
}

/// [`verify_strict_with_derived`], also returning the [`Verified`]
/// diagnostics.
///
/// # Errors
/// Returns [`VerificationError`] on any failing check of §11.6.
pub fn verify_detailed_with_derived(
    derived: &Derived,
    inst: &PublicInstance,
    proof: &Proof,
) -> Result<Verified, VerificationError> {
    let vk = &derived.vk;
    // Step 0 (§11.6): instance checks and derivation for this T.
    // Python's `0 <= exit_code < 2^64` holds by type for `u64`.
    let di = derived.instance(inst.t).map_err(err)?;
    if usize::from(proof.log_t) != di.n {
        return Err(VerificationError::new("proof is for a different T"));
    }
    if proof.root.len() != vk.hasher().digest_size() {
        return Err(VerificationError::new("bad commitment root length"));
    }
    match (vk.pcs, &proof.pcs_proof) {
        (PcsMode::Transparent, PcsProof::Transparent(g)) => {
            let max_bits = om_format::MAX_BYTES * 8;
            let Some(expected_len) = 1usize.checked_shl(di.ell as u32) else {
                return Err(VerificationError::new("ell too large"));
            };
            if expected_len > max_bits || g.len() != expected_len {
                return Err(VerificationError::new(
                    "transparent opening does not match the commitment",
                ));
            }
        }
        (PcsMode::Ligerito, PcsProof::Ligerito(..)) => {}
        _ => {
            return Err(VerificationError::new(
                "pcs proof does not match the vk pcs mode",
            ));
        }
    }
    let (n, s) = (di.n, di.s);
    // Canonical output (§14.3) and fitting input, via the encoders.
    let words = encode_region(&inst.output, vk.abi.output_log_words).map_err(err)?;
    let m0 = m0_words(vk, &inst.input).map_err(err)?;
    let public = cpu::public_inputs(&derived.program, inst.exit_code);

    // Step 1: statement and commitment absorption, as the prover.
    let mut tr = Transcript::new(LABEL, vk.hasher());
    absorb_statement(&mut tr, vk, inst);
    let pcs = absorb_commitment(vk, derived, &di, &proof.root, &mut tr)?;

    // Step 2: Virtual Spartan. Public inputs per SIMD instance are empty (`n_x = 0`),
    // evaluated algebraically in O(nu) without allocating `2^s` vectors.
    let cross = CrossStep {
        in_id: derived.seg_id["S_in"],
        out_id: derived.seg_id["S_out"],
        init: cpu::init_vector(&public),
        fin: cpu::fin_vector(&public),
    };
    let sp_claims = om_spartan::spartan::verify(
        &derived.rels,
        s,
        &[],
        &proof.spartan,
        &mut tr,
        b"vsp",
        None,
        Some(&derived.spartan_segments),
        Some(&cross),
    )?;
    let (virt, direct, xs) = seg_claims(derived, &sp_claims)?;

    // Step 3: register Twist, `M_0 = 0`.
    let (r_o, r_c) = same_point(&virt, &["v1", "v2", "rdv"], 6)?;
    if proof.reg_bits.len() != 3 * REG_A {
        return Err(VerificationError::new("bad register bit claims"));
    }
    let bits: Vec<Vec<K>> = (0..3)
        .map(|x| proof.reg_bits[REG_A * x..REG_A * x + REG_A].to_vec())
        .collect();
    let reg_claims = TwistClaims {
        r_o: r_o.clone(),
        r_c: r_c.clone(),
        rv: vec![virt["v1"].value, virt["v2"].value],
        wv: virt["rdv"].value,
        bits,
    };
    let reg_out = twist_verify(
        &di.reg,
        &|_pt: &[K]| K::ZERO,
        &reg_claims,
        &proof.reg,
        &mut tr,
        b"twist/reg",
        None,
        false,
    )?;

    // Step 4: RAM Twist with final memory; the deterministic
    // `ridx` bit check first, then `y_0` and `wv = rv + y_0`.
    let ram_a = derived.ram_a;
    let (r_or, r_cr) = same_point(&virt, &["rw", "ridx"], 6)?;
    if proof.ram_bits.len() != ram_a {
        return Err(VerificationError::new("bad RAM address-bit claims"));
    }
    if !ram_bits_ok(&r_or, &proof.ram_bits, virt["ridx"].value, ram_a) {
        return Err(VerificationError::new(
            "RAM address bits inconsistent with the ridx segment",
        ));
    }
    let y0 = proof.ram_inc_wv;
    tr.absorb_k(b"twist/ram/incwv", y0);
    let ram_claims = TwistClaims {
        r_o: r_or.clone(),
        r_c: r_cr.clone(),
        rv: vec![virt["rw"].value],
        wv: virt["rw"].value + y0,
        bits: vec![proof.ram_bits.clone(), proof.ram_bits.clone()],
    };
    let o = vk.abi.output_log_words;
    let final_mem = FinalMem {
        m: o as usize,
        s_out: derived.mm.output_base >> o,
        words,
    };
    let m0f = m0_eval(&m0, ram_a);
    let ram_out = twist_verify(
        &di.ram,
        &m0f,
        &ram_claims,
        &proof.ram,
        &mut tr,
        b"twist/ram",
        Some(&final_mem),
        false,
    )?;

    // Step 5: routers (shift on the `Y` claim, store on `y_0`).
    let (r_oy, r_cy) = same_point(&virt, &["Y"], 6)?;
    let sh_claims = shift_verify(
        n,
        &r_oy,
        &r_cy,
        virt["Y"].value,
        &proof.shift,
        &mut tr,
        b"router/shift",
        WORD_BITS,
    )?;
    let st_claims = store_verify(
        n,
        &r_or,
        &r_cr,
        y0,
        &proof.store,
        &mut tr,
        b"router/store",
        WORD_BITS,
    )?;

    // Step 6: bytecode Shout over the derived ROM table and groups.
    let plan = ShoutPlan::new(
        derived,
        n,
        &virt,
        &proof.reg_bits,
        &sh_claims,
        &st_claims[1],
    )?;
    let shout_claims = shout_verify(
        &plan.params,
        &plan.table,
        &plan.groups,
        &proof.shout,
        &mut tr,
        b"shout/bytecode",
    )?;

    // Step 7: Mosaic batch, then ring switching + Ligerito against
    // the root (or the transparent mock's direct opening).
    let mclaims = mosaic_claims(
        &di,
        &direct,
        &xs,
        &reg_out,
        &ram_out,
        &r_or,
        &r_cr,
        y0,
        &sh_claims,
        &st_claims,
        &shout_claims,
    );
    let mosaic_claims = mclaims.len();
    let (r_g, v_g) = batch_verify(&di.layout, &mclaims, &proof.mosaic, &mut tr)?;
    match (vk.pcs, &proof.pcs_proof) {
        (PcsMode::Transparent, PcsProof::Transparent(g)) => {
            let expected_len = 1usize
                .checked_shl(di.ell as u32)
                .ok_or_else(|| VerificationError::new("ell too large"))?;
            if g.len() != expected_len || transparent_root(vk, g) != proof.root {
                return Err(VerificationError::new(
                    "transparent opening does not match the commitment",
                ));
            }
            if mle_eval_bits(g, &r_g) != v_g {
                return Err(VerificationError::new("transparent opening: G(r_G) != v_G"));
            }
        }
        (PcsMode::Ligerito, PcsProof::Ligerito(rs_proof, lig_proof)) => {
            let pcs = pcs.expect("ligerito pcs built at commitment absorption");
            let cm = Commitment {
                root: proof.root.clone(),
                n: pcs.pcs.p.n,
            };
            // Exactly `BitPCS::verify`, without cloning the pair.
            let (r_s, v) = rs_verify(&r_g, v_g, rs_proof, &mut tr)?;
            pcs.pcs.verify(&cm, &r_s, v, lig_proof, &mut tr)?;
        }
        _ => unreachable!("pcs variant checked above"),
    }
    Ok(Verified { mosaic_claims })
}
