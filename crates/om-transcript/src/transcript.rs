//! Fiat-Shamir transcript per spec 02 §2.2–§2.7 (hash chain).
//! Mirrors `reference/openmagnetar/transcript.py` byte for byte.

use om_field::K;

use crate::hashing::Hasher;

/// Domain byte for initialization (`0x00`).
pub const DOM_INIT: u8 = 0x00;
/// Domain byte for absorbing (`0x01`).
pub const DOM_ABSORB: u8 = 0x01;
/// Domain byte for squeezing (`0x02`).
pub const DOM_SQUEEZE: u8 = 0x02;
/// Fixed version label bound at init.
pub const VERSION_LABEL: &[u8] = b"openmagnetar/transcript/v1";

/// The 8-byte little-endian encoding of `n` (spec 02 §2.2).
pub fn u64le(n: u64) -> [u8; 8] {
    n.to_le_bytes()
}

/// Length-prefixed encoding: `u64le(len(x)) || x` (spec 02 §2.2).
pub fn enc(x: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + x.len());
    out.extend_from_slice(&u64le(x.len() as u64));
    out.extend_from_slice(x);
    out
}

fn enc_into(out: &mut Vec<u8>, x: &[u8]) {
    out.extend_from_slice(&u64le(x.len() as u64));
    out.extend_from_slice(x);
}

/// Whether `label` is valid per spec 02 §2.7: non-empty, at most 255 bytes,
/// every byte in `0x21..=0x7E` (printable ASCII, no space).
pub fn is_valid_label(label: &[u8]) -> bool {
    !label.is_empty() && label.len() <= 255 && label.iter().all(|&c| (0x21..=0x7e).contains(&c))
}

fn check_label(label: &[u8]) {
    assert!(
        is_valid_label(label),
        "invalid transcript label: must be non-empty printable ASCII \
         (0x21..=0x7E, no space) of at most 255 bytes, got {label:?}"
    );
}

/// Counter-driven retry shared by exclusion sampling: squeeze via `next`
/// until a nonzero element appears. Factored out so the retry loop can be
/// unit-tested with a stub stream (the Python test subclasses `Hasher`).
fn nonzero_from(mut next: impl FnMut() -> K) -> K {
    loop {
        let c = next();
        if !c.is_zero() {
            return c;
        }
    }
}

/// A hash-chain Fiat-Shamir transcript (spec 02 §2.3): state `S` plus a
/// squeeze counter that absorbing resets to 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transcript {
    hasher: Hasher,
    state: Vec<u8>,
    counter: u64,
}

impl Transcript {
    /// `S = H(0x00 || enc(version) || enc(profile_id) || enc(protocol_label))`,
    /// counter 0.
    ///
    /// # Panics
    /// Panics if `protocol_label` is not a valid label (spec 02 §2.7;
    /// Python raises `ValueError`).
    pub fn new(protocol_label: &[u8], hasher: Hasher) -> Self {
        check_label(protocol_label);
        let mut input = Vec::new();
        input.push(DOM_INIT);
        enc_into(&mut input, VERSION_LABEL);
        enc_into(&mut input, hasher.profile_id());
        enc_into(&mut input, protocol_label);
        Self {
            hasher,
            state: hasher.digest(&input),
            counter: 0,
        }
    }

    /// Convenience constructor with the default SHA-256 profile, mirroring
    /// Python's `Transcript(label)` (`hasher=None`).
    ///
    /// # Panics
    /// Panics if `protocol_label` is not a valid label.
    pub fn new_default(protocol_label: &[u8]) -> Self {
        Self::new(protocol_label, Hasher::Sha256)
    }

    /// The hash profile in use.
    pub fn hasher(&self) -> Hasher {
        self.hasher
    }

    /// The current chain state `S` (`digest_size` bytes). Public for tests
    /// and grinding (Python attribute `state`).
    pub fn state(&self) -> &[u8] {
        &self.state
    }

    /// The current squeeze counter (Python attribute `counter`).
    pub fn counter(&self) -> u64 {
        self.counter
    }

    /// `S = H(0x01 || S || enc(label) || enc(data))`; resets the counter.
    ///
    /// # Panics
    /// Panics if `label` is invalid (spec 02 §2.7).
    pub fn absorb_bytes(&mut self, label: &[u8], data: &[u8]) {
        check_label(label);
        let mut input = Vec::with_capacity(1 + self.state.len() + 16 + label.len() + data.len());
        input.push(DOM_ABSORB);
        input.extend_from_slice(&self.state);
        enc_into(&mut input, label);
        enc_into(&mut input, data);
        self.state = self.hasher.digest(&input);
        self.counter = 0;
    }

    /// Absorb one `K` element as its 16-byte encoding.
    ///
    /// # Panics
    /// Panics if `label` is invalid.
    pub fn absorb_k(&mut self, label: &[u8], x: K) {
        self.absorb_bytes(label, &x.to_bytes());
    }

    /// Absorb a slice of `K` elements as the concatenation of their 16-byte
    /// encodings (16n data bytes; empty slice gives empty data).
    ///
    /// # Panics
    /// Panics if `label` is invalid.
    pub fn absorb_ks(&mut self, label: &[u8], xs: &[K]) {
        let mut data = Vec::with_capacity(16 * xs.len());
        for x in xs {
            data.extend_from_slice(&x.to_bytes());
        }
        self.absorb_bytes(label, &data);
    }

    fn squeeze(&mut self, label: &[u8]) -> Vec<u8> {
        check_label(label);
        let mut input = Vec::with_capacity(1 + self.state.len() + 8 + 8 + label.len());
        input.push(DOM_SQUEEZE);
        input.extend_from_slice(&self.state);
        input.extend_from_slice(&u64le(self.counter));
        enc_into(&mut input, label);
        let out = self.hasher.digest(&input);
        self.counter += 1;
        out
    }

    /// First 16 bytes of a squeeze, decoded per C1.
    ///
    /// # Panics
    /// Panics if `label` is invalid.
    pub fn challenge_k(&mut self, label: &[u8]) -> K {
        let out = self.squeeze(label);
        let bytes: &[u8; 16] = out[..16].try_into().expect("digest >= 16 bytes");
        K::from_bytes(bytes)
    }

    /// `n` successive `challenge_k(label)` calls; `n = 0` squeezes nothing.
    ///
    /// # Panics
    /// Panics if `label` is invalid (only checked when `n > 0`, as in Python).
    pub fn challenge_ks(&mut self, label: &[u8], n: usize) -> Vec<K> {
        (0..n).map(|_| self.challenge_k(label)).collect()
    }

    /// Re-squeeze (next counter value each attempt) until nonzero (spec 02 §2.5).
    ///
    /// # Panics
    /// Panics if `label` is invalid.
    pub fn challenge_nonzero_k(&mut self, label: &[u8]) -> K {
        // check up front so an invalid label fails before consuming a counter
        check_label(label);
        nonzero_from(|| self.challenge_k(label))
    }

    /// Low `bits` bits of the first 8 squeeze bytes (little-endian).
    /// `bits = 0` returns 0 and still consumes one counter value.
    ///
    /// # Panics
    /// Panics if `bits > 64` (Python raises `ValueError`) or if `label`
    /// is invalid. The `bits` check happens before squeezing, as in Python,
    /// so a rejected call consumes no counter value.
    pub fn challenge_index(&mut self, label: &[u8], bits: u32) -> u64 {
        assert!(
            bits <= 64,
            "challenge_index: bits must be in 0..=64, got {bits}"
        );
        let out = self.squeeze(label);
        let v = u64::from_le_bytes(out[..8].try_into().expect("digest >= 8 bytes"));
        if bits == 64 {
            v
        } else {
            v & ((1u64 << bits) - 1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nonzero_retry_consumes_until_nonzero() {
        // Ports test_transcript.py::test_nonzero_retry, which stubs the
        // first two squeezes to zero.
        let mut n = 0u64;
        let c = nonzero_from(|| {
            n += 1;
            if n <= 2 { K::ZERO } else { K::ONE }
        });
        assert_eq!(c, K::ONE);
        assert_eq!(n, 3);
    }

    #[test]
    fn label_validation() {
        assert!(is_valid_label(b"a"));
        assert!(is_valid_label(b"pcs/query/idx"));
        assert!(is_valid_label(&[b'a'; 255]));
        assert!(!is_valid_label(b""));
        assert!(!is_valid_label(&[b'a'; 256]));
        assert!(!is_valid_label(b"has space"));
        assert!(!is_valid_label(b"ctl\x01"));
        assert!(!is_valid_label(b"del\x7f"));
        assert!(!is_valid_label(&[0x80]));
    }
}
