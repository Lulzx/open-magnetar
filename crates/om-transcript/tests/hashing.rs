//! Hash known-answer tests. Expected digests were produced by the Python
//! reference stack (`hashlib`, the same algorithms `hashing.py` wraps) and
//! match the FIPS examples for "", "abc", and the 56-byte message.

use om_transcript::Hasher;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

const MSG56: &[u8] = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";

fn kats(hasher: Hasher, cases: &[(&[u8], &str)]) {
    for (data, want) in cases {
        assert_eq!(&hex(&hasher.digest(data)), want, "len {}", data.len());
    }
}

#[test]
fn sha256_kats() {
    kats(
        Hasher::sha256(),
        &[
            (
                b"",
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                b"abc",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                MSG56,
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
            (
                &[b'a'; 1000],
                "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3",
            ),
        ],
    );
}

#[test]
fn sha3_256_kats() {
    kats(
        Hasher::sha3_256(),
        &[
            (
                b"",
                "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
            ),
            (
                b"abc",
                "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532",
            ),
            (
                MSG56,
                "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376",
            ),
            (
                &[b'a'; 1000],
                "8f3934e6f7a15698fe0f396b95d8c4440929a8fa6eae140171c068b4549fbf81",
            ),
        ],
    );
}

#[test]
fn sha384_kats() {
    kats(
        Hasher::sha384(),
        &[
            (
                b"",
                "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b",
            ),
            (
                b"abc",
                "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7",
            ),
            (
                MSG56,
                "3391fdddfc8dc7393707a65b1b4709397cf8b1d162af05abfe8f450de5f36bc6b0455a8520bc4e6f5fe95b1fe3c8452b",
            ),
            (
                &[b'a'; 1000],
                "f54480689c6b0b11d0303285d9a81b21a93bca6ba5a1b4472765dca4da45ee328082d469c650cd3b61b16d3266ab8ced",
            ),
        ],
    );
}

/// Block/padding-boundary lengths (SHA-256: 55/56/64, SHA3 rate: 135/136/137,
/// SHA-384: 111/112/128), values from Python `hashlib`.
#[test]
fn boundary_lengths() {
    // &[b'a'; N] as &[u8]
    const A: &[u8] = &[b'a'; 256];
    for (n, want) in [
        (
            55,
            "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318",
        ),
        (
            56,
            "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a",
        ),
        (
            64,
            "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb",
        ),
        (
            136,
            "6f0e44b9ce4ea61d52a3479c10f60ef916937f799f11964b7f1c7771063905c4",
        ),
    ] {
        assert_eq!(hex(&Hasher::sha256().digest(&A[..n])), want, "sha256 {n}");
    }
    for (n, want) in [
        (
            135,
            "8094bb53c44cfb1e67b7c30447f9a1c33696d2463ecc1d9c92538913392843c9",
        ),
        (
            136,
            "3fc5559f14db8e453a0a3091edbd2bc25e11528d81c66fa570a4efdcc2695ee1",
        ),
        (
            137,
            "f8d6846cedd2ccfadf15c5879ef95af724d799eed7391fb1c91f95344e738614",
        ),
    ] {
        assert_eq!(hex(&Hasher::sha3_256().digest(&A[..n])), want, "sha3 {n}");
    }
    for (n, want) in [
        (
            111,
            "3c37955051cb5c3026f94d551d5b5e2ac38d572ae4e07172085fed81f8466b8f90dc23a8ffcdea0b8d8e58e8fdacc80a",
        ),
        (
            112,
            "187d4e07cb306103c69967bf544d0dfbe9042577599c73c330abc0cb64c61236d5ed565ee19119d8c31779a38f791fcd",
        ),
        (
            128,
            "edb12730a366098b3b2beac75a3bef1b0969b15c48e2163c23d96994f8d1bef760c7e27f3c464d3829f56c0d53808b0b",
        ),
    ] {
        assert_eq!(hex(&Hasher::sha384().digest(&A[..n])), want, "sha384 {n}");
    }
}

/// Ports reference/tests/test_hashing.py::test_profiles.
#[test]
fn profiles() {
    assert_eq!(Hasher::default(), Hasher::Sha256);
    assert_eq!(Hasher::sha256().profile_id(), b"sha256");
    assert_eq!(Hasher::sha3_256().profile_id(), b"sha3-256");
    assert_eq!(Hasher::sha384().profile_id(), b"sha384");
    assert_eq!(Hasher::sha384().digest_size(), 48);
    assert_eq!(Hasher::sha256().digest_size(), 32);
    assert_eq!(Hasher::sha3_256().digest(b"abc").len(), 32);
    assert_eq!(Hasher::from_profile_id(b"sha256"), Some(Hasher::Sha256));
    assert_eq!(Hasher::from_profile_id(b"sha3-256"), Some(Hasher::Sha3_256));
    assert_eq!(Hasher::from_profile_id(b"sha384"), Some(Hasher::Sha384));
    // Unknown profiles are rejected (Python raises ValueError for "md5").
    assert_eq!(Hasher::from_profile_id(b"md5"), None);
    assert_eq!(Hasher::from_profile_id(b""), None);
    assert_eq!(Hasher::from_profile_id(b"SHA256"), None);
    assert_eq!(Hasher::from_profile_id(b"sha256\0"), None);
}
