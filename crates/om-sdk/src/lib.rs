//! Host SDK for Open Magnetar: the small ergonomic surface a host
//! program uses to keygen, execute, prove and verify guest ELF
//! programs (spec 14 host flow, over `om-prover` / `om-verifier`).
//!
//! The canonical public instance in this SDK is
//! [`om_format::PublicInstance`] — `(T, input, output, exit_code)`,
//! the instance `protocol.prove_instance` returns and
//! `protocol.verify` checks in the reference model, and the one
//! serialized as `OMIN` (§12.3). The other instance type,
//! `om_elf::PublicInstance`, is the §14.3 *statement* form
//! `(program_digest, input, output, exit_code)`: it carries the
//! digest instead of `T`. The two are interconvertible given the vk
//! (whose `program_digest` the statement form duplicates) and `T`;
//! see [`to_statement_instance`] / [`from_statement_instance`]. No
//! semantics are forked: proving and verifying always go through the
//! `T` form, exactly as in Python.
//!
//! No function here panics on user input: underlying failures are
//! returned as [`SdkError`], and panics from sub-crates on malformed
//! input (which the protocol crates treat as programmer errors) are
//! caught at this boundary and reported as [`SdkError::Internal`].

use std::collections::BTreeMap;
use std::fmt;
use std::panic::{AssertUnwindSafe, catch_unwind};

pub use om_elf::Params as AbiParams;
pub use om_elf::PublicInstance as StatementInstance;
pub use om_format::{
    PcsMode, PcsProfile, PublicInstance, VerifyingKey, decode_instance, decode_vk, encode_instance,
    encode_vk, vk_digest,
};
pub use om_transcript::Hasher;

/// Parameters for key generation: the ABI parameters (§14.1) plus the
/// PCS selection. The default is the production profile: Ligerito
/// `provable-120`, SHA-256, `r = 2` (Python `keygen` defaults over
/// `Params()` defaults `A=20, I=12, O=8, MAX_CODE=2^20`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SdkParams {
    /// ABI parameters: `A`/`I`/`O` log word counts, `MAX_CODE`, hash.
    pub abi: AbiParams,
    /// PCS mode (Ligerito, or the test-only transparent mock).
    pub pcs: PcsMode,
    /// PCS profile (`provable-120` or `test`).
    pub pcs_profile: PcsProfile,
    /// `log2(1/rate)` of the Ligerito levels (default 2).
    pub pcs_r: u8,
    /// Queries per level under the `test` profile (must be >= 1
    /// there; ignored under `provable-120`).
    pub pcs_t: u32,
}

impl Default for SdkParams {
    fn default() -> Self {
        SdkParams {
            abi: AbiParams::default(),
            pcs: PcsMode::Ligerito,
            pcs_profile: PcsProfile::Provable120,
            pcs_r: 2,
            pcs_t: 0,
        }
    }
}

impl SdkParams {
    /// The fast profile the reference tests use: Ligerito with the
    /// `test` PCS profile at `pcs_t = 8` queries per level (Python
    /// `make_vk`). Not sound at production levels; for tests only.
    pub fn test_profile() -> Self {
        SdkParams {
            pcs_profile: PcsProfile::Test,
            pcs_t: 8,
            ..SdkParams::default()
        }
    }

    /// Set the ABI parameters (builder style).
    pub fn with_abi(mut self, abi: AbiParams) -> Self {
        self.abi = abi;
        self
    }

    /// Set the hash profile (builder style).
    pub fn with_hash(mut self, hash_profile: Hasher) -> Self {
        self.abi.hash_profile = hash_profile;
        self
    }
}

/// An SDK failure. Every variant wraps the underlying crate's error
/// (whose `Display` is preserved) or states the boundary failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SdkError {
    /// Key generation or derivation failed (`om_prover::KeyError`).
    Key(om_prover::KeyError),
    /// Execution or proving failed (`om_prover::ProverError`).
    Prover(om_prover::ProverError),
    /// A vk/instance/proof blob is malformed (`om_format::FormatError`).
    Format(om_format::FormatError),
    /// The ELF image does not load (`om_elf::ElfError`).
    Elf(om_elf::ElfError),
    /// An ABI bound was violated (`om_elf::AbiError`).
    Abi(om_elf::AbiError),
    /// Verification rejected (`om_verifier::VerificationError`).
    Verification(om_verifier::VerificationError),
    /// The ELF's program digest does not match the vk's: the key was
    /// generated for a different program.
    ProgramMismatch,
    /// The input is invalid at the SDK boundary (e.g. a vk whose
    /// `A` is outside the circuit's supported range).
    InvalidInput(String),
    /// A sub-crate panicked on this input; caught at the boundary
    /// so the SDK itself never panics on user input.
    Internal(String),
}

impl fmt::Display for SdkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SdkError::Key(e) => write!(f, "{e}"),
            SdkError::Prover(e) => write!(f, "{e}"),
            SdkError::Format(e) => write!(f, "{e}"),
            SdkError::Elf(e) => write!(f, "{e}"),
            SdkError::Abi(e) => write!(f, "{e}"),
            SdkError::Verification(e) => write!(f, "{e}"),
            SdkError::ProgramMismatch => {
                f.write_str("ELF program does not match the verifying key (program digest)")
            }
            SdkError::InvalidInput(m) => f.write_str(m),
            SdkError::Internal(m) => write!(f, "internal error: {m}"),
        }
    }
}

impl std::error::Error for SdkError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            SdkError::Key(e) => Some(e),
            SdkError::Prover(e) => Some(e),
            SdkError::Format(e) => Some(e),
            SdkError::Elf(e) => Some(e),
            SdkError::Abi(e) => Some(e),
            SdkError::Verification(e) => Some(e),
            _ => None,
        }
    }
}

impl From<om_prover::KeyError> for SdkError {
    fn from(e: om_prover::KeyError) -> SdkError {
        SdkError::Key(e)
    }
}

impl From<om_prover::ProverError> for SdkError {
    fn from(e: om_prover::ProverError) -> SdkError {
        SdkError::Prover(e)
    }
}

impl From<om_format::FormatError> for SdkError {
    fn from(e: om_format::FormatError) -> SdkError {
        SdkError::Format(e)
    }
}

impl From<om_elf::ElfError> for SdkError {
    fn from(e: om_elf::ElfError) -> SdkError {
        SdkError::Elf(e)
    }
}

impl From<om_elf::AbiError> for SdkError {
    fn from(e: om_elf::AbiError) -> SdkError {
        SdkError::Abi(e)
    }
}

impl From<om_verifier::VerificationError> for SdkError {
    fn from(e: om_verifier::VerificationError) -> SdkError {
        SdkError::Verification(e)
    }
}

/// Run `f`, converting any panic into [`SdkError::Internal`] (the
/// no-panic-on-user-input boundary).
fn guard<T>(f: impl FnOnce() -> Result<T, SdkError>) -> Result<T, SdkError> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(payload) => {
            let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "sub-crate panicked on this input".to_string()
            };
            Err(SdkError::Internal(msg))
        }
    }
}

/// Validate a vk before deriving from it (derivation itself assumes a
/// validated key, as in `om-verifier`'s pre-checks).
fn check_vk(vk: &VerifyingKey) -> Result<(), SdkError> {
    vk.validate()?;
    if !(3..=28).contains(&vk.abi.ram_log_words) {
        return Err(SdkError::InvalidInput(
            "vk A (ram_log_words) must satisfy 3 <= A <= 28".to_string(),
        ));
    }
    Ok(())
}

/// Check that `elf_bytes` is the program `vk` was generated for, by
/// loading it under the vk's ABI parameters and comparing program
/// digests (§14.3).
fn check_elf_matches(vk: &VerifyingKey, elf_bytes: &[u8]) -> Result<(), SdkError> {
    let img = om_elf::load(elf_bytes, &vk.abi)?;
    let digest = om_elf::program_digest(&img.code, img.entry_pc, &img.ram_words, &vk.abi);
    if digest != vk.program_digest {
        return Err(SdkError::ProgramMismatch);
    }
    Ok(())
}

/// KeyGen from an ELF64 guest image: load the ELF (§14.2) under
/// `params.abi`, then derive the verifying key (§11.2).
///
/// # Errors
/// Returns [`SdkError`] if the ELF does not load or the parameters
/// do not form a valid key.
pub fn keygen_from_elf(elf_bytes: &[u8], params: &SdkParams) -> Result<VerifyingKey, SdkError> {
    guard(|| {
        let p = params;
        Ok(om_prover::keygen_from_elf(
            elf_bytes,
            p.abi,
            p.pcs,
            p.pcs_profile,
            p.pcs_r,
            p.pcs_t,
        )?)
    })
}

/// KeyGen from a programmatic code/data image (Python `keygen`):
/// `code` maps pc -> instruction word, `data_image` maps RAM word
/// index -> word (non-zero words of the program's data image).
///
/// # Errors
/// Returns [`SdkError`] if the images and parameters do not form a
/// valid key.
pub fn keygen_from_code(
    code: &BTreeMap<u64, u32>,
    entry_pc: u64,
    data_image: &BTreeMap<usize, u64>,
    params: &SdkParams,
) -> Result<VerifyingKey, SdkError> {
    guard(|| {
        let p = params;
        Ok(om_prover::keygen(
            code.clone(),
            entry_pc,
            data_image.clone(),
            p.abi,
            p.pcs,
            p.pcs_profile,
            p.pcs_r,
            p.pcs_t,
        )?)
    })
}

/// Execute the vk's program on `input` without proving, returning
/// `(output, exit_code)`. `elf_bytes` must be the program the vk was
/// generated for (checked by program digest), so a host cannot
/// silently run a different program than it keygenned.
///
/// # Errors
/// Returns [`SdkError`] if the ELF does not match the vk, the input
/// does not fit the input region, execution traps or exceeds the
/// cycle budget, or the output region is non-canonical.
pub fn execute(
    vk: &VerifyingKey,
    elf_bytes: &[u8],
    input: &[u8],
) -> Result<(Vec<u8>, u64), SdkError> {
    guard(|| {
        check_vk(vk)?;
        check_elf_matches(vk, elf_bytes)?;
        execute_input_inner(vk, input)
    })
}

/// [`execute`] without an ELF image: run the program already bound
/// in `vk` (the path for keys built with [`keygen_from_code`]).
///
/// # Errors
/// As [`execute`], minus the ELF checks.
pub fn execute_input(vk: &VerifyingKey, input: &[u8]) -> Result<(Vec<u8>, u64), SdkError> {
    guard(|| {
        check_vk(vk)?;
        execute_input_inner(vk, input)
    })
}

fn execute_input_inner(vk: &VerifyingKey, input: &[u8]) -> Result<(Vec<u8>, u64), SdkError> {
    let ex = om_prover::execute(vk, input, om_prover::DEFAULT_MAX_CYCLES)?;
    Ok((ex.instance.output, ex.exit_code))
}

/// Execute and prove, returning `(public instance, encoded proof
/// blob)`. `elf_bytes` must be the program the vk was generated for
/// (checked by program digest).
///
/// # Errors
/// Returns [`SdkError`] on any execution/proving failure (see
/// [`execute`]).
pub fn prove(
    vk: &VerifyingKey,
    elf_bytes: &[u8],
    input: &[u8],
) -> Result<(PublicInstance, Vec<u8>), SdkError> {
    guard(|| {
        check_vk(vk)?;
        check_elf_matches(vk, elf_bytes)?;
        prove_input_inner(vk, input)
    })
}

/// [`prove`] without an ELF image: prove the program already bound
/// in `vk` (the path for keys built with [`keygen_from_code`]).
///
/// # Errors
/// As [`prove`], minus the ELF checks.
pub fn prove_input(vk: &VerifyingKey, input: &[u8]) -> Result<(PublicInstance, Vec<u8>), SdkError> {
    guard(|| {
        check_vk(vk)?;
        prove_input_inner(vk, input)
    })
}

fn prove_input_inner(
    vk: &VerifyingKey,
    input: &[u8],
) -> Result<(PublicInstance, Vec<u8>), SdkError> {
    let (instance, proof) = om_prover::prove_instance(vk, input, None)?;
    Ok((instance, om_format::encode_proof(vk, &proof)))
}

/// Verify an encoded proof blob against `(vk, instance)` (§11.6, the
/// strict verifier).
///
/// # Errors
/// Returns [`SdkError`] if the vk is invalid, the blob is malformed,
/// or any verifier check rejects.
pub fn verify(
    vk: &VerifyingKey,
    instance: &PublicInstance,
    proof_blob: &[u8],
) -> Result<(), SdkError> {
    guard(|| {
        om_verifier::verify_bytes_strict(vk, instance, proof_blob)?;
        Ok(())
    })
}

/// Byte-oriented [`verify`]: decode the `OMVK` and `OMIN` blobs,
/// then verify the `OMPF` proof blob.
///
/// # Errors
/// Returns [`SdkError`] if any blob is malformed or the proof
/// rejects.
pub fn verify_bytes(
    vk_blob: &[u8],
    instance_blob: &[u8],
    proof_blob: &[u8],
) -> Result<(), SdkError> {
    guard(|| {
        let vk = om_format::decode_vk(vk_blob)?;
        let instance = om_format::decode_instance(instance_blob)?;
        om_verifier::verify_bytes_strict(&vk, &instance, proof_blob)?;
        Ok(())
    })
}

/// The §14.3 statement form of `instance` under `vk`: the vk's
/// `program_digest` in place of `T`.
pub fn to_statement_instance(vk: &VerifyingKey, instance: &PublicInstance) -> StatementInstance {
    StatementInstance {
        program_digest: vk.program_digest,
        input: instance.input.clone(),
        output: instance.output.clone(),
        exit_code: instance.exit_code,
    }
}

/// The canonical (prove/verify) instance for a §14.3 statement and
/// trace length `t`. The statement's digest is not checked here;
/// verification binds it through the vk a caller verifies against.
pub fn from_statement_instance(statement: &StatementInstance, t: u64) -> PublicInstance {
    PublicInstance {
        t,
        input: statement.input.clone(),
        output: statement.output.clone(),
        exit_code: statement.exit_code,
    }
}
