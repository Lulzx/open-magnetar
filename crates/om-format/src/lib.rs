//! Canonical byte encodings of the verifying key, public instance and
//! proof for Open Magnetar.
//!
//! Normative reference: `docs/spec/12-proof-format.md` (with §11.2/11.3
//! for vk content and order, and §13.8 for parser hardening).
//! Behavioral reference: `reference/openmagnetar/proof_format.py`, whose
//! public surface this crate mirrors: [`encode_vk`]/[`decode_vk`],
//! [`encode_instance`]/[`decode_instance`],
//! [`encode_proof`]/[`decode_proof`], [`pcs_free_k_count`],
//! [`ligerito_expected_bytes`], [`FormatError`], [`Reader`].
//!
//! All integers are little-endian; `K` elements are the 16-byte
//! encodings of C1. Lengths that follow from `(vk, T)` are *not*
//! transmitted; the only length prefixes are the `u32` counts inside
//! Ligerito openings, plus the explicit `u64le` lengths of the variable
//! data in the vk and the instance. Parsers reject short input,
//! trailing bytes and any structure that does not match the expected
//! shape, checking every length against the remaining input before
//! allocating (§13.8).
//!
//! Scope split (mirroring the Python dependency direction): this crate
//! owns data types and serialization only. The derived objects of
//! Python's `keygen.Derived` (ROM, relations, layouts) belong to the
//! prover crate; [`decode_proof`] therefore takes the few shape numbers
//! it needs as a [`ProofShape`] supplied by the caller, exactly the
//! quantities `proof_format.decode_proof` reads off `vk.derived`. The
//! two tiny derivations `proof_format.py` itself reaches for —
//! `keygen.choose_ad` and `Derived.ligerito_params` — are ported here
//! as [`choose_ad`] and [`ligerito_params`].
//!
//! Judgment calls where Rust idiom differs from the Python model:
//!
//! - Python's `VerifyingKey.__post_init__` raises `KeyError_`/`AbiError`
//!   for a program-digest mismatch, an `entry_pc` outside the code
//!   image, bad ABI parameters or a `test` profile without queries;
//!   [`decode_vk`] and [`VerifyingKey::new`] report all of these as
//!   [`FormatError`]. The hash profile is the typed [`Hasher`] (via
//!   `om_elf::Params`), so an unknown profile string — which Python's
//!   `decode_vk` accepts and only rejects when `Hasher` is built — is
//!   rejected at parse time.
//! - Python's `protocol.PublicInstance` is `(T, input, output,
//!   exit_code)` and that is what `encode_instance` serializes;
//!   `om_elf::PublicInstance` (spec 14.3) instead carries the program
//!   digest and no `T`, so this crate defines its own
//!   [`PublicInstance`].
//! - Python's `Proof.pcs_proof` is `list[int]` (transparent) or a
//!   `(RingSwitchProof, LigeritoProof)` pair; here it is the enum
//!   [`PcsProof`]. Bit vectors are `Vec<bool>`.
//! - Encoders panic on a malformed in-memory object (a Spartan proof
//!   without the cross-step part, a PCS proof variant that does not
//!   match the vk mode), where Python would raise or mis-encode;
//!   decoders return [`FormatError`] for every malformed input and
//!   never panic on untrusted bytes.
//! - [`MAX_BYTES`] is defined but unused in Python; per §13.8 every
//!   decoder here rejects inputs longer than it before allocating.

use std::collections::BTreeMap;
use std::fmt;

use om_elf::{AbiError, Params, program_digest};
use om_field::K;
use om_memcheck::onehot::{OneHotProof, VirtProof};
use om_memcheck::shout::ShoutProof;
use om_memcheck::twist::TwistProof;
use om_mosaic::BatchProof;
use om_pcs::ligerito::{LevelOpening, LigeritoParams, LigeritoProof, make_params, schedule_with};
use om_pcs::ring_switch::RingSwitchProof;
use om_router::RouterProof;
use om_spartan::SpartanProof;
use om_sumcheck::SumcheckProof;
use om_transcript::Hasher;

/// Magic of a verifying-key blob (§12.2).
pub const MAGIC_VK: [u8; 4] = *b"OMVK";
/// Magic of a public-instance blob (§12.3).
pub const MAGIC_INSTANCE: [u8; 4] = *b"OMIN";
/// Magic of a proof blob (§12.4).
pub const MAGIC_PROOF: [u8; 4] = *b"OMPF";
/// The only vk version defined here (§12.1, `keygen.VK_VERSION`).
pub const VK_VERSION: u8 = 1;
/// The only instance version defined here (§12.3).
pub const INSTANCE_VERSION: u8 = 1;
/// The only proof version defined here (§12.4).
pub const PROOF_VERSION: u8 = 1;
/// Absolute cap on any encoded object; decoders reject longer inputs
/// before allocating (§13.8). Defined but unused in Python.
pub const MAX_BYTES: usize = 1 << 40;
/// Register-file address bits (`keygen.REG_A`): `2^6` registers.
pub const REG_A: usize = 6;
/// Register Twist address components (`keygen.REG_D`).
pub const REG_D: usize = 2;
/// Register Twist reads per cycle (`keygen.REG_P`).
pub const REG_P: usize = 2;
/// Number of bytecode Shout claim groups (§11.7, §12.4 field 8).
pub const SHOUT_GROUPS: usize = 6;
/// `T <= 2^MAX_LOG_T` (§11.3, `keygen.MAX_LOG_T`).
pub const MAX_LOG_T: u32 = 40;

/// A malformed or non-canonical encoding (Python `FormatError`, plus
/// the `KeyError_`/`AbiError` validations Python's `VerifyingKey`
/// constructor performs when `decode_vk` builds the key).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormatError {
    /// Input ended before the last field.
    TruncatedInput,
    /// Input remains after the last field.
    TrailingBytes,
    /// Input longer than [`MAX_BYTES`].
    TooLarge,
    /// Wrong vk magic or version.
    BadVkMagicOrVersion,
    /// Wrong instance magic or version.
    BadInstanceMagicOrVersion,
    /// Wrong proof magic or version.
    BadProofMagicOrVersion,
    /// Hash profile is not one of §2.1's identifiers.
    BadHashProfile,
    /// ABI parameters fail `Params::validate` (§14.1).
    BadAbiParams(AbiError),
    /// Code image has more than `MAX_CODE` words.
    TooManyCodeWords,
    /// Code-image `pc`s are not strictly increasing.
    CodeNotSorted,
    /// Data image is not strictly increasing with non-zero values.
    DataImageNotCanonical,
    /// PCS mode or profile byte is greater than 1.
    BadPcsFields,
    /// Stored `program_digest` differs from the recomputed one (§12.2).
    ProgramDigestMismatch,
    /// `entry_pc` is not a key of the code image (§12.2).
    EntryPcNotInCode,
    /// The `test` PCS profile needs `pcs_t >= 1` (`keygen` check).
    TestProfileNeedsQueries,
    /// `T` is not a power of two in `[4, 2^40]` (§11.3).
    BadT,
    /// The proof header's `log2 T` differs from the instance's (§12.4).
    ProofLogTMismatch,
    /// A Ligerito level opens more columns than its query count (§12.4).
    TooManyOpenedColumns,
    /// A Ligerito level carries more authentication hashes than the
    /// Python bound `64 * columns + 64`.
    TooManyAuthHashes,
    /// A derived shape is impossible for this vk (e.g. `ell` too small
    /// for ring switching plus Ligerito, `keygen` check).
    BadShape(&'static str),
}

impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FormatError::TruncatedInput => f.write_str("truncated input"),
            FormatError::TrailingBytes => f.write_str("trailing bytes"),
            FormatError::TooLarge => f.write_str("input too large"),
            FormatError::BadVkMagicOrVersion => f.write_str("bad vk magic or version"),
            FormatError::BadInstanceMagicOrVersion => f.write_str("bad instance magic or version"),
            FormatError::BadProofMagicOrVersion => f.write_str("bad proof magic or version"),
            FormatError::BadHashProfile => f.write_str("bad hash profile"),
            FormatError::BadAbiParams(e) => write!(f, "{e}"),
            FormatError::TooManyCodeWords => f.write_str("too many code words"),
            FormatError::CodeNotSorted => f.write_str("code not sorted"),
            FormatError::DataImageNotCanonical => f.write_str("data image not canonical"),
            FormatError::BadPcsFields => f.write_str("bad pcs fields"),
            FormatError::ProgramDigestMismatch => f.write_str("program digest mismatch"),
            FormatError::EntryPcNotInCode => f.write_str("bad code image"),
            FormatError::TestProfileNeedsQueries => f.write_str("test profile needs pcs_t >= 1"),
            FormatError::BadT => f.write_str("T must be a power of two in [4, 2^40]"),
            FormatError::ProofLogTMismatch => {
                f.write_str("proof log T does not match the instance")
            }
            FormatError::TooManyOpenedColumns => f.write_str("too many opened columns"),
            FormatError::TooManyAuthHashes => f.write_str("too many authentication hashes"),
            FormatError::BadShape(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for FormatError {}

impl From<AbiError> for FormatError {
    fn from(e: AbiError) -> FormatError {
        FormatError::BadAbiParams(e)
    }
}

/// Cursor over an encoded object (Python `Reader`). Every read checks
/// the remaining length before copying or allocating.
pub struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    /// A reader over `data`; rejects inputs longer than [`MAX_BYTES`].
    ///
    /// # Errors
    /// Returns [`FormatError::TooLarge`] if `data.len() > MAX_BYTES`.
    pub fn new(data: &'a [u8]) -> Result<Reader<'a>, FormatError> {
        if data.len() > MAX_BYTES {
            return Err(FormatError::TooLarge);
        }
        Ok(Reader { data, pos: 0 })
    }

    /// Bytes not yet read.
    pub fn remaining(&self) -> usize {
        self.data.len() - self.pos
    }

    /// The next `n` bytes.
    pub fn take(&mut self, n: usize) -> Result<&'a [u8], FormatError> {
        if n > self.remaining() {
            return Err(FormatError::TruncatedInput);
        }
        let out = &self.data[self.pos..self.pos + n];
        self.pos += n;
        Ok(out)
    }

    /// The next `n` bytes, owned.
    pub fn take_vec(&mut self, n: usize) -> Result<Vec<u8>, FormatError> {
        Ok(self.take(n)?.to_vec())
    }

    /// One byte.
    pub fn u8(&mut self) -> Result<u8, FormatError> {
        Ok(self.take(1)?[0])
    }

    /// A little-endian `u32`.
    pub fn u32(&mut self) -> Result<u32, FormatError> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("4 bytes"),
        ))
    }

    /// A little-endian `u64`.
    pub fn u64(&mut self) -> Result<u64, FormatError> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("8 bytes"),
        ))
    }

    /// One `K` element (every 16-byte string is valid, C1).
    pub fn k(&mut self) -> Result<K, FormatError> {
        Ok(K::from_bytes(self.take(16)?.try_into().expect("16 bytes")))
    }

    /// `n` `K` elements; the byte length is checked before allocating.
    pub fn ks(&mut self, n: usize) -> Result<Vec<K>, FormatError> {
        let bytes = n.checked_mul(16).ok_or(FormatError::TruncatedInput)?;
        let raw = self.take(bytes)?;
        Ok(raw.as_chunks::<16>().0.iter().map(K::from_bytes).collect())
    }

    /// Require the input to be exhausted (no trailing bytes, §12.1).
    pub fn done(&self) -> Result<(), FormatError> {
        if self.pos != self.data.len() {
            return Err(FormatError::TrailingBytes);
        }
        Ok(())
    }
}

fn put_ks(out: &mut Vec<u8>, xs: &[K]) {
    for x in xs {
        out.extend_from_slice(&x.to_bytes());
    }
}

/// `(a, d)`: smallest `d | a` with `a/d <= 4`; if that gives `a/d = 1`
/// (and `a > 1`) `a` is padded up to a multiple of 4 and the rule is
/// applied again (§7.9, Python `keygen.choose_ad`).
///
/// # Panics
/// Panics if `a == 0` (Python finds no divisor and divides by `None`).
pub fn choose_ad(a: usize) -> (usize, usize) {
    fn smallest(a: usize) -> usize {
        (1..=a)
            .find(|d| a.is_multiple_of(*d) && a / d <= 4)
            .expect("choose_ad needs a >= 1")
    }
    let mut a = a;
    let mut d = smallest(a);
    if a > 1 && a / d == 1 {
        a = a.div_ceil(4) * 4;
        d = smallest(a);
    }
    (a, d)
}

// ------------------------------------------------------------------ verifying key

/// PCS mode byte of §12.2 (Python `pcs`: `"ligerito"`/`"transparent"`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum PcsMode {
    /// Ligerito (mode 0).
    #[default]
    Ligerito,
    /// Transparent mock, test only (mode 1, §11.10 #8).
    Transparent,
}

/// PCS profile byte of §12.2 (Python `pcs_profile`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum PcsProfile {
    /// `provable-120` (profile 0): parameters from `make_params`.
    #[default]
    Provable120,
    /// `test` (profile 1): `pcs_t` queries per level.
    Test,
}

/// The program-specific verifying key (§11.2, serialized in §12.2 in
/// field order). Mirrors Python `keygen.VerifyingKey`'s wire fields:
/// `abi`, `code`, `entry_pc`, `m0_program`, `pcs`, `pcs_profile`,
/// `pcs_r`, `pcs_t`, `program_digest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    /// ABI parameters: hash profile, `A`, `I`, `O`, `MAX_CODE`.
    pub abi: Params,
    /// Code image: `pc -> instruction word`.
    pub code: BTreeMap<u64, u32>,
    /// Entry `pc`; a key of `code`.
    pub entry_pc: u64,
    /// Data image: non-zero words of the program's RAM image (RAM word
    /// index -> word), input region excluded.
    pub m0_program: BTreeMap<usize, u64>,
    /// PCS mode (0 Ligerito, 1 transparent mock).
    pub pcs: PcsMode,
    /// PCS profile (0 `provable-120`, 1 `test`).
    pub pcs_profile: PcsProfile,
    /// `log2(1/rate)` of the Ligerito levels.
    pub pcs_r: u8,
    /// Queries per level; used by the `test` profile, 0 otherwise.
    pub pcs_t: u32,
    /// Program digest (§14.3), recomputed and checked by the parser.
    pub program_digest: [u8; 32],
}

impl VerifyingKey {
    /// Build a key, computing `program_digest` (Python `keygen`).
    ///
    /// # Errors
    /// Returns [`FormatError`] for invalid ABI parameters, a `test`
    /// profile with `pcs_t < 1`, a code image over `MAX_CODE`, or an
    /// `entry_pc` outside the code image.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        abi: Params,
        code: BTreeMap<u64, u32>,
        entry_pc: u64,
        m0_program: BTreeMap<usize, u64>,
        pcs: PcsMode,
        pcs_profile: PcsProfile,
        pcs_r: u8,
        pcs_t: u32,
    ) -> Result<VerifyingKey, FormatError> {
        let digest = program_digest(&code, entry_pc, &m0_program, &abi);
        let vk = VerifyingKey {
            abi,
            code,
            entry_pc,
            m0_program,
            pcs,
            pcs_profile,
            pcs_r,
            pcs_t,
            program_digest: digest,
        };
        vk.validate()?;
        Ok(vk)
    }

    /// The Python `VerifyingKey.__post_init__` checks, including the
    /// `program_digest` recomputation §12.2 requires of the parser.
    pub fn validate(&self) -> Result<(), FormatError> {
        self.abi.validate()?;
        if self.pcs_profile == PcsProfile::Test && self.pcs_t < 1 {
            return Err(FormatError::TestProfileNeedsQueries);
        }
        if program_digest(&self.code, self.entry_pc, &self.m0_program, &self.abi)
            != self.program_digest
        {
            return Err(FormatError::ProgramDigestMismatch);
        }
        if self.code.len() as u64 > self.abi.max_code_words {
            return Err(FormatError::TooManyCodeWords);
        }
        if !self.code.contains_key(&self.entry_pc) {
            return Err(FormatError::EntryPcNotInCode);
        }
        Ok(())
    }

    /// The configured hash (Python `vk.hasher`).
    pub fn hasher(&self) -> Hasher {
        self.abi.hash_profile
    }

    /// The RAM Twist address shape `choose_ad(A)` (Python
    /// `Derived.ram_a/ram_d`).
    pub fn ram_ad(&self) -> (usize, usize) {
        choose_ad(self.abi.ram_log_words as usize)
    }

    /// `vk_digest = H("openmagnetar/vk/v1" || encode_vk(vk))` (§11.2).
    pub fn digest(&self) -> Vec<u8> {
        vk_digest(self)
    }
}

/// The canonical `OMVK` encoding of §12.2. The code and data images
/// are emitted in strictly increasing key order with zero data words
/// dropped, exactly as Python's `encode_vk`.
pub fn encode_vk(vk: &VerifyingKey) -> Vec<u8> {
    let a = &vk.abi;
    let prof = a.hash_profile.profile_id();
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC_VK);
    out.push(VK_VERSION);
    out.push(u8::try_from(prof.len()).expect("profile id fits in a byte"));
    out.extend_from_slice(prof);
    for log in [a.ram_log_words, a.input_log_words, a.output_log_words] {
        out.push(u8::try_from(log).expect("log words must fit in a byte"));
    }
    out.extend_from_slice(&a.max_code_words.to_le_bytes());
    out.extend_from_slice(&vk.program_digest);
    out.extend_from_slice(&vk.entry_pc.to_le_bytes());
    out.extend_from_slice(&(vk.code.len() as u64).to_le_bytes());
    for (&pc, &word) in &vk.code {
        out.extend_from_slice(&pc.to_le_bytes());
        out.extend_from_slice(&word.to_le_bytes());
    }
    let nz: Vec<(&usize, &u64)> = vk.m0_program.iter().filter(|&(_, &v)| v != 0).collect();
    out.extend_from_slice(&(nz.len() as u64).to_le_bytes());
    for (&w, &v) in nz {
        out.extend_from_slice(&(w as u64).to_le_bytes());
        out.extend_from_slice(&v.to_le_bytes());
    }
    out.push(match vk.pcs {
        PcsMode::Ligerito => 0,
        PcsMode::Transparent => 1,
    });
    out.push(match vk.pcs_profile {
        PcsProfile::Provable120 => 0,
        PcsProfile::Test => 1,
    });
    out.push(vk.pcs_r);
    out.extend_from_slice(&vk.pcs_t.to_le_bytes());
    out
}

/// Parse an `OMVK` blob (§12.2). Counts are checked against `MAX_CODE`
/// and the remaining input before any allocation; the images must be
/// strictly increasing (data values non-zero); `program_digest` is
/// recomputed and `entry_pc` must be a key of the code image.
pub fn decode_vk(data: &[u8]) -> Result<VerifyingKey, FormatError> {
    let mut r = Reader::new(data)?;
    if r.take(4)? != MAGIC_VK || r.u8()? != VK_VERSION {
        return Err(FormatError::BadVkMagicOrVersion);
    }
    let prof_len = usize::from(r.u8()?);
    let hash_profile =
        Hasher::from_profile_id(r.take(prof_len)?).ok_or(FormatError::BadHashProfile)?;
    let (a, i, o) = (r.u8()?, r.u8()?, r.u8()?);
    let max_code_words = r.u64()?;
    let digest: [u8; 32] = r.take(32)?.try_into().expect("32 bytes");
    let entry_pc = r.u64()?;
    let ncode = r.u64()?;
    if ncode > max_code_words {
        return Err(FormatError::TooManyCodeWords);
    }
    // Each entry is 12 bytes: bound the loop before allocating.
    if u128::from(ncode) * 12 > r.remaining() as u128 {
        return Err(FormatError::TruncatedInput);
    }
    let mut code = BTreeMap::new();
    let mut prev: Option<u64> = None;
    for _ in 0..ncode {
        let (pc, word) = (r.u64()?, r.u32()?);
        if prev.is_some_and(|p| pc <= p) {
            return Err(FormatError::CodeNotSorted);
        }
        code.insert(pc, word);
        prev = Some(pc);
    }
    let nm0 = r.u64()?;
    // Each entry is 16 bytes: bound the loop before allocating.
    if u128::from(nm0) * 16 > r.remaining() as u128 {
        return Err(FormatError::TruncatedInput);
    }
    let mut m0_program = BTreeMap::new();
    let mut prev: Option<u64> = None;
    for _ in 0..nm0 {
        let (w, v) = (r.u64()?, r.u64()?);
        if prev.is_some_and(|p| w <= p) || v == 0 {
            return Err(FormatError::DataImageNotCanonical);
        }
        let w = usize::try_from(w).map_err(|_| FormatError::DataImageNotCanonical)?;
        m0_program.insert(w, v);
        prev = Some(w as u64);
    }
    let (mode, profile, pcs_r, pcs_t) = (r.u8()?, r.u8()?, r.u8()?, r.u32()?);
    r.done()?;
    if mode > 1 || profile > 1 {
        return Err(FormatError::BadPcsFields);
    }
    let vk = VerifyingKey {
        abi: Params {
            ram_log_words: u32::from(a),
            input_log_words: u32::from(i),
            output_log_words: u32::from(o),
            max_code_words,
            hash_profile,
        },
        code,
        entry_pc,
        m0_program,
        pcs: if mode == 0 {
            PcsMode::Ligerito
        } else {
            PcsMode::Transparent
        },
        pcs_profile: if profile == 0 {
            PcsProfile::Provable120
        } else {
            PcsProfile::Test
        },
        pcs_r,
        pcs_t,
        program_digest: digest,
    };
    vk.validate()?;
    Ok(vk)
}

/// `vk_digest = H("openmagnetar/vk/v1" || encode_vk(vk))` (§11.2),
/// `H.digest_size` bytes.
pub fn vk_digest(vk: &VerifyingKey) -> Vec<u8> {
    let mut preimage = b"openmagnetar/vk/v1".to_vec();
    preimage.extend_from_slice(&encode_vk(vk));
    vk.hasher().digest(&preimage)
}

/// The Ligerito parameters for a committed `G` with `ell` variables
/// (Python `Derived.ligerito_params`): packed `n = ell - 7`;
/// `make_params` for `provable-120`, else `schedule(n, final =
/// min(6, n-1))` with `pcs_t` queries and rate `pcs_r` per level.
///
/// # Errors
/// Returns [`FormatError::BadShape`] if `ell - 7 < 2`, or (for
/// `provable-120`, whose schedule leaves 6 final variables) if
/// `ell - 7 <= 6`, or if a `test`-profile level would have rate 0.
pub fn ligerito_params(vk: &VerifyingKey, ell: usize) -> Result<LigeritoParams, FormatError> {
    let n = ell
        .checked_sub(7)
        .filter(|&n| n >= 2)
        .ok_or(FormatError::BadShape(
            "G too small for ring switching + Ligerito",
        ))?;
    match vk.pcs_profile {
        PcsProfile::Provable120 => {
            if n <= 6 || vk.pcs_r < 1 {
                return Err(FormatError::BadShape("G too small for provable-120"));
            }
            Ok(make_params(n, "provable-120", usize::from(vk.pcs_r)))
        }
        PcsProfile::Test => {
            if vk.pcs_r < 1 || vk.pcs_t < 1 {
                return Err(FormatError::BadShape("bad test-profile pcs fields"));
            }
            let ks = schedule_with(n, 6.min(n - 1), 5);
            let levels = ks.len();
            Ok(LigeritoParams::new(
                n,
                ks,
                vec![usize::from(vk.pcs_r); levels],
                vec![vk.pcs_t as usize; levels],
            ))
        }
    }
}

// ------------------------------------------------------------------ instance

/// The public instance as serialized in §12.3 (Python
/// `protocol.PublicInstance`): trace length, public input and output,
/// exit code. Distinct from `om_elf::PublicInstance` (§14.3), which
/// carries the program digest instead of `T`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicInstance {
    /// Trace length `T` (a power of two, checked by the verifier).
    pub t: u64,
    /// Public input bytes.
    pub input: Vec<u8>,
    /// Public output bytes.
    pub output: Vec<u8>,
    /// `a0` at HALT.
    pub exit_code: u64,
}

/// The canonical `OMIN` encoding of §12.3.
pub fn encode_instance(inst: &PublicInstance) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC_INSTANCE);
    out.push(INSTANCE_VERSION);
    out.extend_from_slice(&inst.t.to_le_bytes());
    out.extend_from_slice(&(inst.input.len() as u64).to_le_bytes());
    out.extend_from_slice(&inst.input);
    out.extend_from_slice(&(inst.output.len() as u64).to_le_bytes());
    out.extend_from_slice(&inst.output);
    out.extend_from_slice(&inst.exit_code.to_le_bytes());
    out
}

/// Parse an `OMIN` blob (§12.3). Like Python's `decode_instance` this
/// checks only the framing; the §12.3 verifier checks (`4 <= T = 2^n
/// <= 2^40`, canonical output) belong to the verifier.
pub fn decode_instance(data: &[u8]) -> Result<PublicInstance, FormatError> {
    let mut r = Reader::new(data)?;
    if r.take(4)? != MAGIC_INSTANCE || r.u8()? != INSTANCE_VERSION {
        return Err(FormatError::BadInstanceMagicOrVersion);
    }
    let t = r.u64()?;
    let n_in = usize::try_from(r.u64()?).map_err(|_| FormatError::TruncatedInput)?;
    let input = r.take_vec(n_in)?;
    let n_out = usize::try_from(r.u64()?).map_err(|_| FormatError::TruncatedInput)?;
    let output = r.take_vec(n_out)?;
    let exit_code = r.u64()?;
    r.done()?;
    Ok(PublicInstance {
        t,
        input,
        output,
        exit_code,
    })
}

// ------------------------------------------------------------------ proof shapes

/// The shape numbers [`decode_proof`] needs that are functions of the
/// vk but not stored in it — exactly what Python's `decode_proof`
/// reads off `vk.derived` and `Derived.instance(T)`. Deriving them
/// (ROM expansion, circuit layout, Mosaic layout) is the prover
/// crate's job; `T` itself is passed separately, as in Python.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofShape {
    /// Spartan row bits `rho` (Python `Derived.rho`, 10 by default).
    pub rho: usize,
    /// Spartan column bits `nu` (Python `Derived.nu`, 14 by default).
    pub nu: usize,
    /// Number of witness segments (Python `len(Derived.segments)`).
    pub num_segments: usize,
    /// Bytecode Shout address bits `a_B` (Python `Derived.rom_a`).
    pub rom_a: usize,
    /// Bytecode Shout address components `d_B` (Python `Derived.rom_d`).
    pub rom_d: usize,
    /// Variables of the committed `G` (Python `Instance.ell`).
    pub ell: usize,
}

/// The field shapes of a Twist proof (Python `twist_shape` dict), for
/// address bits `a`, components `d`, reads `p`, cycles `2^n`, and the
/// optional final-memory part. Sum-check shapes are `(rounds, degree)`
/// message counts in `K` elements per round (C3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TwistShape {
    /// `rw` sum-check: `(n + a, 3)`.
    pub rw: (usize, usize),
    /// `rw_evals` count: `p + 3`.
    pub rw_ev: usize,
    /// `val` sum-check: `(n, 3)`; its evals are always 2.
    pub val: (usize, usize),
    /// `fin` sum-check: `(n, 2)` when `final_mem`; its evals are 2.
    pub fin: Option<(usize, usize)>,
    /// Virtualization sum-check `(n, d + 1)` when `d > 1`.
    pub virt: Option<(usize, usize)>,
    /// Virtualization evals: `(p + 1 + final_mem) * d`.
    pub virt_ev: usize,
    /// One-hot sum-check: `(n, 4)`.
    pub oh: (usize, usize),
    /// One-hot evals, flattened: `2 * (p + 1) * d`.
    pub oh_ev: usize,
}

/// The Twist proof shapes of §12.4 fields 3/5 (Python `twist_shape`).
pub fn twist_shape(a: usize, d: usize, p: usize, n: usize, final_mem: bool) -> TwistShape {
    let ngroups = p + 1 + usize::from(final_mem);
    TwistShape {
        rw: (n + a, 3),
        rw_ev: p + 3,
        val: (n, 3),
        fin: final_mem.then_some((n, 2)),
        virt: (d > 1).then_some((n, d + 1)),
        virt_ev: ngroups * d,
        oh: (n, 4),
        oh_ev: 2 * (p + 1) * d,
    }
}

fn sc_write(out: &mut Vec<u8>, sc: &SumcheckProof) {
    for m in &sc.round_msgs {
        put_ks(out, m);
    }
}

fn sc_read(r: &mut Reader<'_>, rounds: usize, deg: usize) -> Result<SumcheckProof, FormatError> {
    let mut round_msgs = Vec::new();
    for _ in 0..rounds {
        round_msgs.push(r.ks(deg)?);
    }
    Ok(SumcheckProof { round_msgs })
}

fn twist_write(out: &mut Vec<u8>, pr: &TwistProof) {
    sc_write(out, &pr.rw);
    put_ks(out, &pr.rw_evals);
    sc_write(out, &pr.val);
    put_ks(out, &pr.val_evals);
    if let Some(fin) = &pr.fin {
        sc_write(out, fin);
        put_ks(
            out,
            pr.fin_evals
                .as_deref()
                .expect("twist fin proof without fin evals"),
        );
    }
    if let Some(virt) = &pr.virt {
        sc_write(out, &virt.sc);
        put_ks(out, &virt.evals);
    }
    sc_write(out, &pr.onehot.sc);
    for e in &pr.onehot.evals {
        put_ks(out, e);
    }
}

fn twist_read(
    r: &mut Reader<'_>,
    a: usize,
    d: usize,
    p: usize,
    n: usize,
    final_mem: bool,
) -> Result<TwistProof, FormatError> {
    let sh = twist_shape(a, d, p, n, final_mem);
    let rw = sc_read(r, sh.rw.0, sh.rw.1)?;
    let rw_evals = r.ks(sh.rw_ev)?;
    let val = sc_read(r, sh.val.0, sh.val.1)?;
    let val_evals = r.ks(2)?;
    let (fin, fin_evals) = match sh.fin {
        Some((rounds, deg)) => (Some(sc_read(r, rounds, deg)?), Some(r.ks(2)?)),
        None => (None, None),
    };
    let virt = match sh.virt {
        Some((rounds, deg)) => Some(VirtProof {
            sc: sc_read(r, rounds, deg)?,
            evals: r.ks(sh.virt_ev)?,
        }),
        None => None,
    };
    let oh_sc = sc_read(r, sh.oh.0, sh.oh.1)?;
    let flat = r.ks(sh.oh_ev)?;
    let evals = flat
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| pair.to_vec())
        .collect();
    Ok(TwistProof {
        rw,
        rw_evals,
        val,
        val_evals,
        fin,
        fin_evals,
        inc_extra: None,
        virt,
        onehot: OneHotProof { sc: oh_sc, evals },
    })
}

fn shout_write(out: &mut Vec<u8>, pr: &ShoutProof) {
    sc_write(out, &pr.read);
    put_ks(out, &pr.ra_evals);
    if let Some(virt) = &pr.virt {
        sc_write(out, &virt.sc);
        put_ks(out, &virt.evals);
    }
    sc_write(out, &pr.onehot.sc);
    for e in &pr.onehot.evals {
        put_ks(out, e);
    }
}

fn shout_read(r: &mut Reader<'_>, a: usize, d: usize, n: usize) -> Result<ShoutProof, FormatError> {
    let read = sc_read(r, a, 2)?;
    let ra_evals = r.ks(SHOUT_GROUPS)?;
    let virt = if d > 1 {
        Some(VirtProof {
            sc: sc_read(r, n, d + 1)?,
            evals: r.ks(d)?,
        })
    } else {
        None
    };
    let oh_sc = sc_read(r, n, 4)?;
    let flat = r.ks(2 * d)?;
    Ok(ShoutProof {
        read,
        ra_evals,
        virt,
        onehot: OneHotProof {
            sc: oh_sc,
            evals: flat
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| pair.to_vec())
                .collect(),
        },
    })
}

// -------------------------------------------------------- Ligerito / ring switching

fn lig_write(out: &mut Vec<u8>, pf: &LigeritoProof) {
    for root in &pf.roots {
        out.extend_from_slice(root);
    }
    for sc in &pf.sumchecks {
        sc_write(out, sc);
    }
    for op in &pf.openings {
        out.extend_from_slice(
            &u32::try_from(op.columns.len())
                .expect("column count fits in u32")
                .to_le_bytes(),
        );
        for col in &op.columns {
            put_ks(out, col);
        }
        out.extend_from_slice(
            &u32::try_from(op.auth.len())
                .expect("auth count fits in u32")
                .to_le_bytes(),
        );
        for h in &op.auth {
            out.extend_from_slice(h);
        }
    }
    put_ks(out, &pf.final_poly);
}

fn lig_read(
    r: &mut Reader<'_>,
    p: &LigeritoParams,
    dsz: usize,
) -> Result<LigeritoProof, FormatError> {
    let mut roots = Vec::new();
    for _ in 0..p.levels() - 1 {
        roots.push(r.take_vec(dsz)?);
    }
    let mut sumchecks = Vec::new();
    for &k in &p.ks {
        sumchecks.push(sc_read(r, k, 2)?);
    }
    let mut openings = Vec::new();
    for (i, &k) in p.ks.iter().enumerate() {
        let nc = r.u32()? as usize;
        if nc > p.ts[i] {
            return Err(FormatError::TooManyOpenedColumns);
        }
        let col_len = 1usize
            .checked_shl(k as u32)
            .ok_or(FormatError::BadShape("Ligerito fold arity too large"))?;
        let mut columns = Vec::new();
        for _ in 0..nc {
            columns.push(r.ks(col_len)?);
        }
        let na = r.u32()? as usize;
        if na > nc * 64 + 64 {
            return Err(FormatError::TooManyAuthHashes);
        }
        let mut auth = Vec::new();
        for _ in 0..na {
            auth.push(r.take_vec(dsz)?);
        }
        openings.push(LevelOpening { columns, auth });
    }
    let final_len = 1usize
        .checked_shl(p.n_final() as u32)
        .ok_or(FormatError::BadShape("Ligerito final size too large"))?;
    Ok(LigeritoProof {
        roots,
        sumchecks,
        openings,
        final_poly: r.ks(final_len)?,
    })
}

// ------------------------------------------------------------------ proof

/// The PCS part of a proof (§12.4 field 10; Python `pcs_proof`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PcsProof {
    /// Transparent mock: the committed bit vector `G` in the clear.
    Transparent(Vec<bool>),
    /// Ring switching, then the Ligerito opening.
    Ligerito(RingSwitchProof, LigeritoProof),
}

/// An aggregated proof, in transcript order (§11.5, §12.4). Mirrors
/// Python `protocol.Proof` field for field: `log_t`, `root`,
/// `spartan`, `reg_bits`, `reg`, `ram_bits`, `ram_inc_wv`, `ram`,
/// `shift`, `store`, `shout`, `mosaic`, `pcs_proof`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    /// `log2 T`, repeated as a consistency check (§12.1).
    pub log_t: u8,
    /// PCS commitment root, `H.digest_size` bytes.
    pub root: Vec<u8>,
    /// Virtual Spartan (§12.4 field 1).
    pub spartan: SpartanProof,
    /// Register-index bit claims, `3 * REG_A` elements (field 2).
    pub reg_bits: Vec<K>,
    /// Register Twist (field 3).
    pub reg: TwistProof,
    /// RAM address-bit claims, `ram_a` elements (field 4).
    pub ram_bits: Vec<K>,
    /// `y_0 = Inc~(r_o || r_c)` of the RAM Twist (field 4).
    pub ram_inc_wv: K,
    /// RAM Twist with final memory (field 5).
    pub ram: TwistProof,
    /// Shift router (field 6).
    pub shift: RouterProof,
    /// Store router (field 7).
    pub store: RouterProof,
    /// Bytecode Shout (field 8).
    pub shout: ShoutProof,
    /// Mosaic batch (field 9).
    pub mosaic: BatchProof,
    /// PCS opening (field 10).
    pub pcs_proof: PcsProof,
}

/// The canonical `OMPF` encoding of §12.4, fields in transcript
/// order. No lengths are emitted beyond the Ligerito `u32` counts:
/// every other size is a function of `(vk, T)` (§12.1).
///
/// # Panics
/// Panics if the Spartan proof has no cross-step part, a Twist `fin`
/// proof has no `fin_evals`, or `pcs_proof`'s variant does not match
/// `vk.pcs` (programmer errors; Python would mis-encode or raise).
pub fn encode_proof(vk: &VerifyingKey, pr: &Proof) -> Vec<u8> {
    let sp = &pr.spartan;
    let mut out = Vec::new();
    out.extend_from_slice(&MAGIC_PROOF);
    out.push(PROOF_VERSION);
    out.push(pr.log_t);
    out.extend_from_slice(&pr.root);
    for t in 0..2 {
        for m in &sp.outer_msgs[t] {
            put_ks(&mut out, m);
        }
    }
    for t in 0..2 {
        put_ks(&mut out, &sp.outer_finals[t]);
    }
    sc_write(&mut out, &sp.inner);
    out.extend_from_slice(&sp.v_w.to_bytes());
    put_ks(&mut out, &sp.seg_vals);
    sc_write(
        &mut out,
        sp.xs_proof
            .as_ref()
            .expect("spartan proof without cross-step sum-check"),
    );
    put_ks(
        &mut out,
        sp.xs_vals
            .as_deref()
            .expect("spartan proof without cross-step values"),
    );
    put_ks(&mut out, &pr.reg_bits);
    twist_write(&mut out, &pr.reg);
    put_ks(&mut out, &pr.ram_bits);
    out.extend_from_slice(&pr.ram_inc_wv.to_bytes());
    twist_write(&mut out, &pr.ram);
    sc_write(&mut out, &pr.shift.sc);
    put_ks(&mut out, &pr.shift.evals);
    sc_write(&mut out, &pr.store.sc);
    put_ks(&mut out, &pr.store.evals);
    shout_write(&mut out, &pr.shout);
    sc_write(&mut out, &pr.mosaic.sumcheck);
    out.extend_from_slice(&pr.mosaic.v_g.to_bytes());
    match (vk.pcs, &pr.pcs_proof) {
        (PcsMode::Transparent, PcsProof::Transparent(g)) => {
            // Bit i = bit (i mod 8) of byte i / 8 (§12.4).
            let mut bytes = vec![0u8; g.len().div_ceil(8)];
            for (i, &b) in g.iter().enumerate() {
                if b {
                    bytes[i / 8] |= 1 << (i % 8);
                }
            }
            out.extend_from_slice(&bytes);
        }
        (PcsMode::Ligerito, PcsProof::Ligerito(rs, lp)) => {
            put_ks(&mut out, &rs.s);
            sc_write(&mut out, &rs.sumcheck);
            lig_write(&mut out, lp);
        }
        _ => panic!("pcs proof variant does not match the vk pcs mode"),
    }
    out
}

/// Parse an `OMPF` blob for this vk and trace length (§12.4), with
/// the derived [`ProofShape`]. Mirrors Python
/// `decode_proof(vk, data, T)`, which derives the shape itself.
pub fn decode_proof(
    vk: &VerifyingKey,
    data: &[u8],
    t: u64,
    shape: &ProofShape,
) -> Result<Proof, FormatError> {
    if t < 4 || !t.is_power_of_two() || t > (1u64 << MAX_LOG_T) {
        return Err(FormatError::BadT);
    }
    let n = t.trailing_zeros() as usize;
    let s = n - 2;
    let ell = shape.ell;
    let mut r = Reader::new(data)?;
    if r.take(4)? != MAGIC_PROOF || r.u8()? != PROOF_VERSION {
        return Err(FormatError::BadProofMagicOrVersion);
    }
    if usize::from(r.u8()?) != n {
        return Err(FormatError::ProofLogTMismatch);
    }
    let dsz = vk.hasher().digest_size();
    let root = r.take_vec(dsz)?;
    let mut outer_msgs = Vec::new();
    for _ in 0..2 {
        let mut msgs = Vec::new();
        for _ in 0..shape.rho + s {
            msgs.push(r.ks(3)?);
        }
        outer_msgs.push(msgs);
    }
    let mut outer_finals = Vec::new();
    for _ in 0..2 {
        outer_finals.push(r.ks(3)?);
    }
    let inner = sc_read(&mut r, shape.nu, 2)?;
    let v_w = r.k()?;
    let seg_vals = r.ks(shape.num_segments)?;
    let xs_proof = sc_read(&mut r, 8 + s, 2)?;
    let xs_vals = r.ks(2)?;
    let spartan = SpartanProof {
        outer_msgs,
        outer_finals,
        inner,
        v_w,
        seg_vals,
        xs_proof: Some(xs_proof),
        xs_vals: Some(xs_vals),
    };
    let reg_bits = r.ks(3 * REG_A)?;
    let reg = twist_read(&mut r, REG_A, REG_D, REG_P, n, false)?;
    let (ram_a, ram_d) = vk.ram_ad();
    let ram_bits = r.ks(ram_a)?;
    let ram_inc_wv = r.k()?;
    let ram = twist_read(&mut r, ram_a, ram_d, 1, n, true)?;
    let shift = RouterProof {
        sc: sc_read(&mut r, n + 15, 4)?,
        evals: r.ks(3)?,
    };
    let store = RouterProof {
        sc: sc_read(&mut r, n + 9, 6)?,
        evals: r.ks(5)?,
    };
    let shout = shout_read(&mut r, shape.rom_a, shape.rom_d, n)?;
    let mosaic = BatchProof {
        sumcheck: sc_read(&mut r, ell, 2)?,
        v_g: r.k()?,
    };
    let pcs_proof = match vk.pcs {
        PcsMode::Transparent => {
            let nbits = 1usize
                .checked_shl(ell as u32)
                .ok_or(FormatError::BadShape("ell too large"))?;
            let nb = if ell >= 3 { nbits / 8 } else { 1 };
            let bytes = r.take(nb)?;
            PcsProof::Transparent(
                (0..nbits)
                    .map(|i| (bytes[i / 8] >> (i % 8)) & 1 == 1)
                    .collect(),
            )
        }
        PcsMode::Ligerito => {
            let p = ligerito_params(vk, ell)?;
            let rs = RingSwitchProof {
                s: r.ks(128)?,
                sumcheck: sc_read(&mut r, ell - 7, 2)?,
            };
            PcsProof::Ligerito(rs, lig_read(&mut r, &p, dsz)?)
        }
    };
    r.done()?;
    Ok(Proof {
        log_t: u8::try_from(n).expect("n <= 40"),
        root,
        spartan,
        reg_bits,
        reg,
        ram_bits,
        ram_inc_wv,
        ram,
        shift,
        store,
        shout,
        mosaic,
        pcs_proof,
    })
}

// ------------------------------------------------------------------ size model

/// Number of `K` elements of the proof outside the PCS opening
/// (exact), as a function of the shape (§12.5; Python
/// `pcs_free_k_count`, whose defaults are `rho = 10`, `nu = 14`,
/// `reg_d = 2`).
///
/// # Panics
/// Panics on a nonsensical shape (`n < 2` or `ell < 7`).
#[allow(clippy::too_many_arguments)]
pub fn pcs_free_k_count(
    n: usize,
    ram_a: usize,
    ram_d: usize,
    rom_a: usize,
    rom_d: usize,
    ell: usize,
    num_segments: usize,
    rho: usize,
    nu: usize,
    reg_d: usize,
) -> usize {
    let ni = i128::try_from(n).expect("n fits in i128");
    let elli = i128::try_from(ell).expect("ell fits in i128");
    let s = ni - 2;
    // Spartan (§6.7).
    let mut cnt: i128 =
        2 * 3 * (rho as i128 + s) + 6 + 2 * nu as i128 + 1 + num_segments as i128 + 2 * (8 + s) + 2;
    cnt += 3 * REG_A as i128;
    for (a, d, p, fin) in [
        (REG_A as i128, reg_d as i128, 2i128, false),
        (ram_a as i128, ram_d as i128, 1i128, true),
    ] {
        let ngroups = p + 1 + i128::from(fin);
        cnt += 3 * (ni + a) + (p + 3) + 3 * ni + 2;
        if fin {
            cnt += 2 * ni + 2;
        }
        if d > 1 {
            cnt += (d + 1) * ni + ngroups * d;
        }
        cnt += 4 * ni + 2 * (p + 1) * d;
    }
    cnt += ram_a as i128 + 1;
    cnt += 4 * (ni + 15) + 3 + 6 * (ni + 9) + 5;
    cnt += 2 * rom_a as i128 + SHOUT_GROUPS as i128 + 4 * ni + 2 * rom_d as i128;
    if rom_d > 1 {
        cnt += (rom_d as i128 + 1) * ni + rom_d as i128;
    }
    cnt += 2 * elli + 1;
    cnt += 128 + 2 * (elli - 7); // ring switching
    usize::try_from(cnt).expect("pcs_free_k_count shape gives a negative count")
}

/// Expected size in bytes of a `LigeritoProof` encoding (uniform
/// random queries, sorted distinct), Python
/// `ligerito_expected_bytes`.
pub fn ligerito_expected_bytes(p: &LigeritoParams, digest_size: usize) -> f64 {
    let mut total = (digest_size * (p.levels() - 1) + 16 * (1usize << p.n_final())) as f64;
    for i in 0..p.levels() {
        let (n_cw, t, k) = (
            (1usize << p.log_codeword(i)) as f64,
            p.ts[i] as f64,
            p.ks[i],
        );
        let distinct = n_cw * (1.0 - (1.0 - 1.0 / n_cw).powf(t));
        let depth = p.log_codeword(i);
        // Expected auth hashes of a deduplicated multi-path: sum over
        // levels of siblings not in the set.
        let mut auth = 0.0;
        for lvl in 0..depth {
            let nodes = (1usize << (depth - lvl)) as f64;
            let occ = nodes * (1.0 - (1.0 - 1.0 / nodes).powf(t));
            auth += occ * (1.0 - 1.0 / nodes).powf(t);
        }
        total +=
            8.0 + (16 * k * 2) as f64 + distinct * (16 << k) as f64 + auth * digest_size as f64;
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kv(v: u128) -> K {
        K::from_u128(v)
    }

    fn ks_from(start: u128, n: usize) -> Vec<K> {
        (0..n).map(|i| kv(start + i as u128 * 0x9e37 + 1)).collect()
    }

    fn sc(rounds: usize, deg: usize, seed: u128) -> SumcheckProof {
        SumcheckProof {
            round_msgs: (0..rounds)
                .map(|i| ks_from(seed + i as u128 * 101, deg))
                .collect(),
        }
    }

    fn twist(a: usize, d: usize, p: usize, n: usize, fin: bool, seed: u128) -> TwistProof {
        let sh = twist_shape(a, d, p, n, fin);
        TwistProof {
            rw: sc(sh.rw.0, sh.rw.1, seed),
            rw_evals: ks_from(seed + 1, sh.rw_ev),
            val: sc(sh.val.0, sh.val.1, seed + 2),
            val_evals: ks_from(seed + 3, 2),
            fin: sh.fin.map(|(r, dg)| sc(r, dg, seed + 4)),
            fin_evals: sh.fin.map(|_| ks_from(seed + 5, 2)),
            inc_extra: None,
            virt: sh.virt.map(|(r, dg)| VirtProof {
                sc: sc(r, dg, seed + 6),
                evals: ks_from(seed + 7, sh.virt_ev),
            }),
            onehot: OneHotProof {
                sc: sc(sh.oh.0, sh.oh.1, seed + 8),
                evals: (0..sh.oh_ev / 2)
                    .map(|i| ks_from(seed + 9 + i as u128, 2))
                    .collect(),
            },
        }
    }

    fn shout(a: usize, d: usize, n: usize, seed: u128) -> ShoutProof {
        ShoutProof {
            read: sc(a, 2, seed),
            ra_evals: ks_from(seed + 1, SHOUT_GROUPS),
            virt: (d > 1).then(|| VirtProof {
                sc: sc(n, d + 1, seed + 2),
                evals: ks_from(seed + 3, d),
            }),
            onehot: OneHotProof {
                sc: sc(n, 4, seed + 4),
                evals: (0..d).map(|i| ks_from(seed + 5 + i as u128, 2)).collect(),
            },
        }
    }

    fn vk(pcs: PcsMode) -> VerifyingKey {
        VerifyingKey::new(
            Params {
                ram_log_words: 4,
                input_log_words: 1,
                output_log_words: 1,
                max_code_words: 256,
                hash_profile: Hasher::Sha256,
            },
            BTreeMap::from([(0x1000, 0x0000_0073), (0x1004, 0x0010_0093)]),
            0x1000,
            BTreeMap::from([(3usize, 42u64), (7, u64::MAX)]),
            pcs,
            PcsProfile::Test,
            2,
            8,
        )
        .expect("valid vk")
    }

    /// A synthetic shape: N=n at T=32; rom_d=2 exercises the Shout
    /// virtualization, ram choose_ad(4)=(4,1) the d=1 Twist branch.
    fn shape(ell: usize) -> ProofShape {
        ProofShape {
            rho: 10,
            nu: 14,
            num_segments: 37,
            rom_a: 4,
            rom_d: 2,
            ell,
        }
    }

    fn proof(vk: &VerifyingKey, shape: &ProofShape) -> Proof {
        let (n, s) = (5usize, 3usize);
        let (ram_a, ram_d) = vk.ram_ad();
        let pcs_proof = match vk.pcs {
            PcsMode::Transparent => {
                PcsProof::Transparent((0..1usize << shape.ell).map(|i| i % 3 == 0).collect())
            }
            PcsMode::Ligerito => {
                let p = ligerito_params(vk, shape.ell).expect("params");
                let lp = LigeritoProof {
                    roots: (0..p.levels() - 1).map(|_| vec![7u8; 32]).collect(),
                    sumchecks: p.ks.iter().map(|&k| sc(k, 2, 500)).collect(),
                    openings: p
                        .ks
                        .iter()
                        .map(|&k| LevelOpening {
                            columns: vec![ks_from(600, 1 << k), ks_from(700, 1 << k)],
                            auth: vec![vec![9u8; 32]; 3],
                        })
                        .collect(),
                    final_poly: ks_from(800, 1 << p.n_final()),
                };
                PcsProof::Ligerito(
                    RingSwitchProof {
                        s: ks_from(900, 128),
                        sumcheck: sc(shape.ell - 7, 2, 1000),
                    },
                    lp,
                )
            }
        };
        Proof {
            log_t: n as u8,
            root: vec![5u8; 32],
            spartan: SpartanProof {
                outer_msgs: (0..2)
                    .map(|t| {
                        (0..shape.rho + s)
                            .map(|i| ks_from(t * 100 + i as u128, 3))
                            .collect()
                    })
                    .collect(),
                outer_finals: (0..2).map(|t| ks_from(200 + t, 3)).collect(),
                inner: sc(shape.nu, 2, 300),
                v_w: kv(0xabcd),
                seg_vals: ks_from(400, shape.num_segments),
                xs_proof: Some(sc(8 + s, 2, 500)),
                xs_vals: Some(ks_from(600, 2)),
            },
            reg_bits: ks_from(700, 3 * REG_A),
            reg: twist(REG_A, REG_D, REG_P, n, false, 2000),
            ram_bits: ks_from(800, ram_a),
            ram_inc_wv: kv(0x1234),
            ram: twist(ram_a, ram_d, 1, n, true, 3000),
            shift: RouterProof {
                sc: sc(n + 15, 4, 4000),
                evals: ks_from(4001, 3),
            },
            store: RouterProof {
                sc: sc(n + 9, 6, 5000),
                evals: ks_from(5001, 5),
            },
            shout: shout(shape.rom_a, shape.rom_d, n, 6000),
            mosaic: BatchProof {
                sumcheck: sc(shape.ell, 2, 7000),
                v_g: kv(0x7777),
            },
            pcs_proof,
        }
    }

    #[test]
    fn vk_roundtrip() {
        for mode in [PcsMode::Ligerito, PcsMode::Transparent] {
            let vk = vk(mode);
            let blob = encode_vk(&vk);
            let back = decode_vk(&blob).expect("decode vk");
            assert_eq!(back, vk);
            assert_eq!(encode_vk(&back), blob);
            assert_eq!(back.digest(), vk_digest(&vk));
        }
    }

    #[test]
    fn instance_roundtrip() {
        let inst = PublicInstance {
            t: 32,
            input: b"hello".to_vec(),
            output: vec![13, 0, 0, 0, 0, 0, 0, 0],
            exit_code: 7,
        };
        let blob = encode_instance(&inst);
        assert_eq!(decode_instance(&blob).expect("decode"), inst);
    }

    #[test]
    fn proof_roundtrip_ligerito() {
        let vk = vk(PcsMode::Ligerito);
        let sh = shape(16);
        let pr = proof(&vk, &sh);
        let blob = encode_proof(&vk, &pr);
        let back = decode_proof(&vk, &blob, 32, &sh).expect("decode proof");
        assert_eq!(back, pr);
        assert_eq!(encode_proof(&vk, &back), blob);
        // Size model is exact outside the PCS opening (Python
        // test_size_model): total - ligerito = header + 16 * N_K.
        let (ram_a, ram_d) = vk.ram_ad();
        let k = pcs_free_k_count(
            5,
            ram_a,
            ram_d,
            sh.rom_a,
            sh.rom_d,
            sh.ell,
            sh.num_segments,
            sh.rho,
            sh.nu,
            REG_D,
        );
        let PcsProof::Ligerito(_, lp) = &pr.pcs_proof else {
            panic!("ligerito")
        };
        let mut lig = Vec::new();
        lig_write(&mut lig, lp);
        assert_eq!(blob.len() - lig.len(), 4 + 2 + 32 + 16 * k);
    }

    #[test]
    fn proof_roundtrip_transparent() {
        let vk = vk(PcsMode::Transparent);
        let sh = shape(8);
        let pr = proof(&vk, &sh);
        let blob = encode_proof(&vk, &pr);
        let back = decode_proof(&vk, &blob, 32, &sh).expect("decode proof");
        assert_eq!(back, pr);
        assert_eq!(encode_proof(&vk, &back), blob);
    }

    #[test]
    fn vk_truncation_every_prefix() {
        let blob = encode_vk(&vk(PcsMode::Ligerito));
        for len in 0..blob.len() {
            assert!(decode_vk(&blob[..len]).is_err(), "prefix {len} accepted");
        }
        let mut long = blob.clone();
        long.push(0);
        assert_eq!(decode_vk(&long), Err(FormatError::TrailingBytes));
    }

    #[test]
    fn vk_negatives() {
        let vk = vk(PcsMode::Ligerito);
        let blob = encode_vk(&vk);
        let mut bad_magic = blob.clone();
        bad_magic[0] ^= 1;
        assert_eq!(decode_vk(&bad_magic), Err(FormatError::BadVkMagicOrVersion));
        let mut bad_ver = blob.clone();
        bad_ver[4] = 2;
        assert_eq!(decode_vk(&bad_ver), Err(FormatError::BadVkMagicOrVersion));
        // program_digest field: after magic+ver+proflen+"sha256"+AIO+MAX_CODE.
        let dig_off = 4 + 1 + 1 + 6 + 3 + 8;
        let mut bad_dig = blob.clone();
        bad_dig[dig_off] ^= 1;
        assert_eq!(decode_vk(&bad_dig), Err(FormatError::ProgramDigestMismatch));
        // Tamper a code word: digest no longer matches either.
        let mut bad_code = blob.clone();
        let last_word = bad_code.len() - 7 - 16 * 2 - 8 - 4;
        bad_code[last_word] ^= 1;
        assert!(decode_vk(&bad_code).is_err());
        // entry_pc not in code (also breaks the digest, so build the
        // in-memory key and validate directly).
        let mut bad_entry = vk.clone();
        bad_entry.entry_pc = 0x2000;
        bad_entry.program_digest = program_digest(
            &bad_entry.code,
            bad_entry.entry_pc,
            &bad_entry.m0_program,
            &bad_entry.abi,
        );
        assert_eq!(
            decode_vk(&encode_vk(&bad_entry)),
            Err(FormatError::EntryPcNotInCode)
        );
        // Count overrun: ncode = MAX_CODE + 1.
        let mut over = blob.clone();
        let ncode_off = dig_off + 32 + 8;
        over[ncode_off..ncode_off + 8].copy_from_slice(&257u64.to_le_bytes());
        assert_eq!(decode_vk(&over), Err(FormatError::TooManyCodeWords));
        // Count within MAX_CODE but beyond the input.
        let mut over2 = blob.clone();
        over2[ncode_off..ncode_off + 8].copy_from_slice(&200u64.to_le_bytes());
        assert_eq!(decode_vk(&over2), Err(FormatError::TruncatedInput));
        // Bad PCS mode byte (last 7 bytes are mode, profile, r, t).
        let mut bad_pcs = blob.clone();
        let m = bad_pcs.len() - 7;
        bad_pcs[m] = 2;
        assert_eq!(decode_vk(&bad_pcs), Err(FormatError::BadPcsFields));
        // Unknown hash profile.
        let mut bad_hash = blob.clone();
        bad_hash[6] = b'x';
        assert_eq!(decode_vk(&bad_hash), Err(FormatError::BadHashProfile));
    }

    #[test]
    fn instance_and_proof_negatives() {
        let inst = PublicInstance {
            t: 32,
            input: vec![1, 2],
            output: vec![3],
            exit_code: 0,
        };
        let ib = encode_instance(&inst);
        assert!(decode_instance(&ib[..ib.len() - 1]).is_err());
        let mut long = ib.clone();
        long.push(0);
        assert_eq!(decode_instance(&long), Err(FormatError::TrailingBytes));
        let mut bad = ib.clone();
        bad[4] = 9;
        assert_eq!(
            decode_instance(&bad),
            Err(FormatError::BadInstanceMagicOrVersion)
        );
        // Huge input length must be rejected before allocation.
        let mut huge = ib.clone();
        huge[13..21].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(decode_instance(&huge).is_err());

        let vk = vk(PcsMode::Ligerito);
        let sh = shape(16);
        let blob = encode_proof(&vk, &proof(&vk, &sh));
        assert!(decode_proof(&vk, &blob[..blob.len() - 1], 32, &sh).is_err());
        let mut long = blob.clone();
        long.push(0);
        assert_eq!(
            decode_proof(&vk, &long, 32, &sh),
            Err(FormatError::TrailingBytes)
        );
        assert_eq!(
            decode_proof(&vk, &blob, 64, &sh),
            Err(FormatError::ProofLogTMismatch)
        );
        assert_eq!(decode_proof(&vk, &blob, 48, &sh), Err(FormatError::BadT));
        let mut bad_ver = blob.clone();
        bad_ver[4] = 2;
        assert_eq!(
            decode_proof(&vk, &bad_ver, 32, &sh),
            Err(FormatError::BadProofMagicOrVersion)
        );
    }

    #[test]
    fn size_model_matches_python() {
        // Values computed by reference/openmagnetar/proof_format.py.
        assert_eq!(pcs_free_k_count(5, 4, 1, 4, 2, 16, 37, 10, 14, REG_D), 795);
        let p = LigeritoParams::new(9, vec![3], vec![2], vec![8]);
        let got = ligerito_expected_bytes(&p, 32);
        assert!((got - 3_201.436_712_470_223).abs() < 1e-6, "{got}");
    }

    #[test]
    fn choose_ad_matches_python_rule() {
        assert_eq!(choose_ad(4), (4, 1));
        assert_eq!(choose_ad(6), (6, 2));
        assert_eq!(choose_ad(20), (20, 5));
        assert_eq!(choose_ad(24), (24, 6));
        assert_eq!(choose_ad(2), (2, 1));
        assert_eq!(choose_ad(5), (8, 2)); // a/d = 1 pads to a multiple of 4
        assert_eq!(choose_ad(16), (16, 4));
    }
}
