//! Hash profiles per spec 02 §2.1, implemented from scratch (no hash crates):
//! SHA-256 and SHA-384 (FIPS 180-4) and SHA3-256 (FIPS 202).

/// A fixed hash profile. Mirrors Python `Hasher` in
/// `reference/openmagnetar/hashing.py`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Hasher {
    /// SHA-256 (default), 32-byte output, profile id `b"sha256"`.
    #[default]
    Sha256,
    /// SHA3-256, 32-byte output, profile id `b"sha3-256"`.
    Sha3_256,
    /// SHA-384, 48-byte output, profile id `b"sha384"`.
    Sha384,
}

impl Hasher {
    /// The `sha256` profile (default).
    pub const fn sha256() -> Self {
        Self::Sha256
    }
    /// The `sha3-256` profile.
    pub const fn sha3_256() -> Self {
        Self::Sha3_256
    }
    /// The `sha384` profile.
    pub const fn sha384() -> Self {
        Self::Sha384
    }

    /// Look up a profile by its exact identifier bytes (spec 02 §2.1).
    /// Returns `None` for an unknown profile, which callers MUST reject
    /// (Python `Hasher` raises `ValueError`).
    pub fn from_profile_id(id: &[u8]) -> Option<Self> {
        match id {
            b"sha256" => Some(Self::Sha256),
            b"sha3-256" => Some(Self::Sha3_256),
            b"sha384" => Some(Self::Sha384),
            _ => None,
        }
    }

    /// The profile identifier as a string (Python `Hasher.profile`).
    pub const fn profile(&self) -> &'static str {
        match self {
            Self::Sha256 => "sha256",
            Self::Sha3_256 => "sha3-256",
            Self::Sha384 => "sha384",
        }
    }

    /// The exact ASCII profile-id bytes absorbed by the transcript at init
    /// (no terminator).
    pub const fn profile_id(&self) -> &'static [u8] {
        match self {
            Self::Sha256 => b"sha256",
            Self::Sha3_256 => b"sha3-256",
            Self::Sha384 => b"sha384",
        }
    }

    /// Output size in bytes: 32 for SHA-256/SHA3-256, 48 for SHA-384.
    pub const fn digest_size(&self) -> usize {
        match self {
            Self::Sha256 | Self::Sha3_256 => 32,
            Self::Sha384 => 48,
        }
    }

    /// Hash `data`, returning `digest_size()` bytes.
    pub fn digest(&self, data: &[u8]) -> Vec<u8> {
        match self {
            Self::Sha256 => crate::sha256::digest(data).to_vec(),
            Self::Sha3_256 => crate::keccak::sha3_256(data).to_vec(),
            Self::Sha384 => crate::sha512::sha384(data).to_vec(),
        }
    }
}
