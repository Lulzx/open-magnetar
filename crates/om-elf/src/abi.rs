//! Guest ABI: memory map, I/O encoding, program digest (spec section 14).
//!
//! Mirrors `reference/openmagnetar/abi.py`. Word indices are RAM word
//! indices: word `w` is at byte address `RAM_BASE + 8 * w` (C5).

use std::collections::BTreeMap;
use std::fmt;

use om_field::K;
use om_transcript::Hasher;

/// First RAM byte address (C5).
pub const RAM_BASE: u64 = 0x8000_0000;
/// Default linker placement of code (informative).
pub const CODE_BASE: u64 = 0x1000_0000;
/// `2^64 - 1`.
pub const MASK64: u64 = u64::MAX;
/// Domain separator of the program digest (14.3).
pub const DIGEST_DOMAIN: &[u8] = b"open-magnetar/program/v1";

/// An ABI violation (Python `AbiError`, a `ValueError`). The `Display`
/// strings reproduce the Python messages exactly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiError {
    /// `I` or `O` below 1.
    IoLogWordsTooSmall,
    /// `max(I, O) + 1 > A`.
    IoWindowTooLarge,
    /// `A > 40`.
    RamTooLarge,
    /// `max_code_words < 1`.
    MaxCodeWordsTooSmall,
    /// Data (plus its length word) does not fit in the region.
    RegionTooSmall,
    /// Region word slice has the wrong length.
    WrongRegionSize,
    /// The length word declares more data than the region holds.
    DeclaredLengthExceedsRegion,
    /// Non-zero padding: the region is not the canonical encoding.
    NonCanonicalRegion,
    /// A program data word lies in the I/O window or outside RAM.
    ProgramDataOutsideRam,
    /// MLE point length is not `O + 6`.
    WrongPointLength,
}

impl fmt::Display for AbiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            AbiError::IoLogWordsTooSmall => "I and O must be >= 1",
            AbiError::IoWindowTooLarge => "2^(max(I,O)+1) must not exceed 2^A",
            AbiError::RamTooLarge => "A too large",
            AbiError::MaxCodeWordsTooSmall => "max_code_words must be >= 1",
            AbiError::RegionTooSmall => "data does not fit in region",
            AbiError::WrongRegionSize => "wrong region size",
            AbiError::DeclaredLengthExceedsRegion => "declared length exceeds region",
            AbiError::NonCanonicalRegion => "non-canonical region (non-zero padding)",
            AbiError::ProgramDataOutsideRam => "program data overlaps I/O window or is outside RAM",
            AbiError::WrongPointLength => "point has wrong length",
        })
    }
}

impl std::error::Error for AbiError {}

/// Verifying-key parameters relevant to the ABI (14.1). Mirrors Python
/// `Params`; `hash_profile` is the typed [`Hasher`] instead of a string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Params {
    /// `A`: RAM has `2^A` words.
    pub ram_log_words: u32,
    /// `I`: input region has `2^I` words.
    pub input_log_words: u32,
    /// `O`: output region has `2^O` words.
    pub output_log_words: u32,
    /// Maximum number of 32-bit instructions (`MAX_CODE`).
    pub max_code_words: u64,
    /// Hash profile (C4); `sha256` by default.
    pub hash_profile: Hasher,
}

impl Default for Params {
    fn default() -> Self {
        Params {
            ram_log_words: 20,
            input_log_words: 12,
            output_log_words: 8,
            max_code_words: 1 << 20,
            hash_profile: Hasher::Sha256,
        }
    }
}

impl Params {
    /// `Params(A, I, O)` with the default `max_code_words` and hash profile.
    pub fn new(ram_log_words: u32, input_log_words: u32, output_log_words: u32) -> Self {
        Params {
            ram_log_words,
            input_log_words,
            output_log_words,
            ..Params::default()
        }
    }

    /// Check `1 <= I, O`, `max(I, O) + 1 <= A`, `A <= 40` and
    /// `max_code_words >= 1` (14.1).
    pub fn validate(&self) -> Result<(), AbiError> {
        let m = self.input_log_words.max(self.output_log_words);
        if self.input_log_words < 1 || self.output_log_words < 1 {
            return Err(AbiError::IoLogWordsTooSmall);
        }
        if m + 1 > self.ram_log_words {
            return Err(AbiError::IoWindowTooLarge);
        }
        if self.ram_log_words > 40 {
            return Err(AbiError::RamTooLarge);
        }
        if self.max_code_words < 1 {
            return Err(AbiError::MaxCodeWordsTooSmall);
        }
        Ok(())
    }
}

/// The RAM layout induced by [`Params`] (14.1). All values are RAM word
/// indices unless named `*_addr`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryMap {
    /// Total RAM words, `2^A`.
    pub ram_words: usize,
    /// First word of the I/O window (= `input_base`); the stack top.
    pub io_window_base: usize,
    /// First word of the input region.
    pub input_base: usize,
    /// First word of the output region.
    pub output_base: usize,
    /// Input region size, `2^I` words.
    pub input_words: usize,
    /// Output region size, `2^O` words.
    pub output_words: usize,
    /// Initial `sp` (byte address).
    pub stack_top_addr: u64,
    /// Byte address of the input region.
    pub input_addr: u64,
    /// Byte address of the output region.
    pub output_addr: u64,
}

/// Compute the memory map (14.1). Validates `p` first, as in Python.
pub fn memory_map(p: &Params) -> Result<MemoryMap, AbiError> {
    p.validate()?;
    let m = p.input_log_words.max(p.output_log_words);
    let n = 1usize << p.ram_log_words;
    let in_base = n - (1usize << (m + 1));
    let out_base = in_base + (1usize << m);
    Ok(MemoryMap {
        ram_words: n,
        io_window_base: in_base,
        input_base: in_base,
        output_base: out_base,
        input_words: 1usize << p.input_log_words,
        output_words: 1usize << p.output_log_words,
        stack_top_addr: RAM_BASE + 8 * in_base as u64,
        input_addr: RAM_BASE + 8 * in_base as u64,
        output_addr: RAM_BASE + 8 * out_base as u64,
    })
}

fn region_size(log_words: u32) -> usize {
    1usize
        .checked_shl(log_words)
        .expect("region log_words too large")
}

/// Canonical region encoding (14.1): `[len, packed words...]`, zero padded
/// to `2^log_words` words. Requires `1 + ceil(len/8) <= 2^log_words`.
pub fn encode_region(data: &[u8], log_words: u32) -> Result<Vec<u64>, AbiError> {
    let size = region_size(log_words);
    let nw = data.len().div_ceil(8);
    if 1 + nw > size {
        return Err(AbiError::RegionTooSmall);
    }
    let mut words = vec![0u64; size];
    words[0] = data.len() as u64;
    for i in 0..nw {
        let mut buf = [0u8; 8];
        let chunk = &data[8 * i..(8 * i + 8).min(data.len())];
        buf[..chunk.len()].copy_from_slice(chunk);
        words[1 + i] = u64::from_le_bytes(buf);
    }
    Ok(words)
}

/// Inverse of [`encode_region`]; errors unless the region is canonical
/// (length fits, every padding byte and trailing word is zero).
pub fn decode_region(words: &[u64], log_words: u32) -> Result<Vec<u8>, AbiError> {
    let size = region_size(log_words);
    if words.len() != size {
        return Err(AbiError::WrongRegionSize);
    }
    let n = words[0];
    // Compare in u128: a hostile length word near 2^64 must not overflow.
    if 1 + u128::from(n).div_ceil(8) > size as u128 {
        return Err(AbiError::DeclaredLengthExceedsRegion);
    }
    let nw = (n as usize).div_ceil(8);
    let mut data = Vec::with_capacity(8 * nw);
    for &w in &words[1..1 + nw] {
        data.extend_from_slice(&w.to_le_bytes());
    }
    data.truncate(n as usize);
    if encode_region(&data, log_words)? != words {
        return Err(AbiError::NonCanonicalRegion);
    }
    Ok(data)
}

/// Sparse `M_0` contribution of the input: word index → value, non-zero
/// words only.
pub fn input_words(data: &[u8], p: &Params) -> Result<BTreeMap<usize, u64>, AbiError> {
    let mm = memory_map(p)?;
    let w = encode_region(data, p.input_log_words)?;
    Ok(w.into_iter()
        .enumerate()
        .filter(|&(_, v)| v != 0)
        .map(|(i, v)| (mm.input_base + i, v))
        .collect())
}

/// Full initial memory `M_0` = program data image + input region (14.3).
/// Program words are copied verbatim (Python keeps zero values if given).
pub fn build_m0(
    program_ram: &BTreeMap<usize, u64>,
    data: &[u8],
    p: &Params,
) -> Result<BTreeMap<usize, u64>, AbiError> {
    let mm = memory_map(p)?;
    if program_ram.keys().any(|&w| w >= mm.io_window_base) {
        return Err(AbiError::ProgramDataOutsideRam);
    }
    let mut m0 = program_ram.clone();
    m0.extend(input_words(data, p)?);
    Ok(m0)
}

/// The output-region words of a sparse final RAM (missing words read 0).
/// Python's dict form of `output_region_words`.
pub fn output_region_words(
    final_ram: &BTreeMap<usize, u64>,
    p: &Params,
) -> Result<Vec<u64>, AbiError> {
    let mm = memory_map(p)?;
    Ok((0..region_size(p.output_log_words))
        .map(|i| final_ram.get(&(mm.output_base + i)).copied().unwrap_or(0))
        .collect())
}

/// The output-region words of a dense final RAM. Python's list form.
///
/// # Panics
/// Panics if the slice does not cover the output region (Python raises
/// `IndexError`).
pub fn output_region_words_slice(final_ram: &[u64], p: &Params) -> Result<Vec<u64>, AbiError> {
    let mm = memory_map(p)?;
    Ok((0..region_size(p.output_log_words))
        .map(|i| final_ram[mm.output_base + i])
        .collect())
}

/// Output bytes from a sparse final RAM; errors if non-canonical.
pub fn extract_output(final_ram: &BTreeMap<usize, u64>, p: &Params) -> Result<Vec<u8>, AbiError> {
    decode_region(&output_region_words(final_ram, p)?, p.output_log_words)
}

/// Output bytes from a dense final RAM; errors if non-canonical.
///
/// # Panics
/// Panics if the slice does not cover the output region.
pub fn extract_output_slice(final_ram: &[u64], p: &Params) -> Result<Vec<u8>, AbiError> {
    decode_region(
        &output_region_words_slice(final_ram, p)?,
        p.output_log_words,
    )
}

/// Bit table of the expected output region, index `o + 64 * w` (bit `o` of
/// word `w`; C2, C5). Length `2^(O+6)`.
///
/// Informative only: 07's final-memory claim uses its own layout (see the
/// integration notes of spec 14); this helper is kept and tested.
pub fn output_region_bits(output: &[u8], p: &Params) -> Result<Vec<bool>, AbiError> {
    let words = encode_region(output, p.output_log_words)?;
    Ok(words
        .iter()
        .flat_map(|&v| (0..64).map(move |o| (v >> o) & 1 == 1))
        .collect())
}

/// MLE of the expected output-region bit table at `r` (length `O + 6`,
/// `x_1` the in-word bit LSB, then word-index bits).
pub fn expected_output_mle_eval(output: &[u8], p: &Params, r: &[K]) -> Result<K, AbiError> {
    if r.len() != p.output_log_words as usize + 6 {
        return Err(AbiError::WrongPointLength);
    }
    Ok(om_sumcheck::mle_eval_bits(
        &output_region_bits(output, p)?,
        r,
    ))
}

/// Hash of the canonical program image (code, entry, data image, ABI
/// params), per 14.3. `ram_words` contributes only its non-zero words.
///
/// The digest is the first 32 bytes of the configured hash `H` (14.3):
/// the whole output for `sha256`/`sha3-256`, truncated for the 48-byte
/// `sha384` profile, so the field is 32 bytes under every profile (12.2).
/// Python does not validate `p` here; neither does this.
///
/// # Panics
/// Panics if a log-words parameter exceeds 255 (Python `bytes([...])`
/// raises `ValueError`).
pub fn program_digest(
    code: &BTreeMap<u64, u32>,
    entry_pc: u64,
    ram_words: &BTreeMap<usize, u64>,
    p: &Params,
) -> [u8; 32] {
    let mut preimage = Vec::new();
    preimage.extend_from_slice(DIGEST_DOMAIN);
    for log in [p.ram_log_words, p.input_log_words, p.output_log_words] {
        preimage.push(u8::try_from(log).expect("log words must fit in a byte"));
    }
    preimage.extend_from_slice(&p.max_code_words.to_le_bytes());
    preimage.extend_from_slice(&entry_pc.to_le_bytes());
    preimage.extend_from_slice(&(code.len() as u64).to_le_bytes());
    for (&pc, &word) in code {
        preimage.extend_from_slice(&pc.to_le_bytes());
        preimage.extend_from_slice(&word.to_le_bytes());
    }
    let nz: Vec<(&usize, &u64)> = ram_words.iter().filter(|&(_, &v)| v != 0).collect();
    preimage.extend_from_slice(&(nz.len() as u64).to_le_bytes());
    for (&w, &v) in nz {
        preimage.extend_from_slice(&(w as u64).to_le_bytes());
        preimage.extend_from_slice(&v.to_le_bytes());
    }
    let digest = p.hash_profile.digest(&preimage);
    digest[..32]
        .try_into()
        .expect("every profile digest is at least 32 bytes")
}

/// The public instance of a claim (14.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicInstance {
    /// Digest binding the program image and ABI params.
    pub program_digest: [u8; 32],
    /// Public input bytes.
    pub input: Vec<u8>,
    /// Public output bytes.
    pub output: Vec<u8>,
    /// `a0` at HALT.
    pub exit_code: u64,
}
