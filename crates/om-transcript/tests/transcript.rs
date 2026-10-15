//! Ports reference/tests/test_transcript.py and checks the spec §2.8 known
//! answers plus the JSON vectors in reference/vectors/02-transcript/.

use std::path::PathBuf;

use om_field::K;
use om_transcript::{Hasher, Transcript, enc, u64le};
use serde_json::Value;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The script of test_transcript.py::script / spec §2.8. Returns the outputs
/// as JSON values in the same shape as the vector file.
fn script(t: &mut Transcript) -> Vec<Value> {
    t.absorb_bytes(b"test/bytes", b"hello");
    t.absorb_k(b"test/k", K::from_u128(0x0123_4567_89AB_CDEF));
    t.absorb_ks(b"test/ks", &[K::from_u128(1), K::X, K::t(3)]);
    vec![
        Value::String(t.challenge_k(b"test/c1").to_hex()),
        Value::String(t.challenge_k(b"test/c1").to_hex()),
        Value::Array(
            t.challenge_ks(b"test/cs", 2)
                .iter()
                .map(|x| Value::String(x.to_hex()))
                .collect(),
        ),
        Value::String(t.challenge_nonzero_k(b"test/nz").to_hex()),
        Value::Number(t.challenge_index(b"test/idx", 20).into()),
        // i64 exceeds i64::MAX possibly; serde_json Number from u64 works.
        Value::Number(t.challenge_index(b"test/idx64", 64).into()),
    ]
}

#[test]
fn deterministic_and_sensitive() {
    let a = script(&mut Transcript::new_default(b"om/test"));
    assert_eq!(a, script(&mut Transcript::new_default(b"om/test")));
    assert_ne!(a, script(&mut Transcript::new_default(b"om/test2")));
    assert_ne!(
        a,
        script(&mut Transcript::new(b"om/test", Hasher::sha3_256()))
    );
    assert_ne!(a[0], a[1]); // counter separates same-label squeezes
}

#[test]
fn framing_unambiguous() {
    let (mut t1, mut t2) = (
        Transcript::new_default(b"om/x"),
        Transcript::new_default(b"om/x"),
    );
    t1.absorb_bytes(b"a", b"bc");
    t2.absorb_bytes(b"ab", b"c");
    assert_ne!(t1.challenge_k(b"c"), t2.challenge_k(b"c"));
}

#[test]
fn known_answer_manual() {
    let h = Hasher::sha256();
    let mut init = vec![0x00];
    init.extend(enc(b"openmagnetar/transcript/v1"));
    init.extend(enc(b"sha256"));
    init.extend(enc(b"om/test"));
    let mut st = h.digest(&init);
    let mut t = Transcript::new_default(b"om/test");
    assert_eq!(t.state(), &st[..]);

    t.absorb_bytes(b"lbl", b"data");
    let mut absorb = vec![0x01];
    absorb.extend_from_slice(&st);
    absorb.extend(enc(b"lbl"));
    absorb.extend(enc(b"data"));
    st = h.digest(&absorb);
    assert_eq!(t.state(), &st[..]);
    assert_eq!(t.counter(), 0);

    let mut sq = vec![0x02];
    sq.extend_from_slice(&st);
    sq.extend(u64le(0));
    sq.extend(enc(b"ch"));
    let out = h.digest(&sq);
    assert_eq!(
        t.challenge_k(b"ch"),
        K::from_bytes(out[..16].try_into().unwrap())
    );

    let mut sq = vec![0x02];
    sq.extend_from_slice(&st);
    sq.extend(u64le(1));
    sq.extend(enc(b"ch"));
    let out = h.digest(&sq);
    let want = u64::from_le_bytes(out[..8].try_into().unwrap()) & 1023;
    assert_eq!(t.challenge_index(b"ch", 10), want);
    assert_eq!(t.counter(), 2);
}

#[test]
fn nonzero_is_nonzero_and_consumes_one() {
    // The zero-retry loop itself is unit-tested inside the crate (the Rust
    // Hasher is an enum and cannot be stubbed like the Python subclass).
    let mut t = Transcript::new_default(b"om/t");
    let c = t.challenge_nonzero_k(b"nz");
    assert!(!c.is_zero());
    assert_eq!(t.counter(), 1);
}

#[test]
fn index_range() {
    let mut t = Transcript::new_default(b"om/t");
    for bits in [0u32, 1, 7, 64] {
        let v = t.challenge_index(b"i", bits);
        if bits == 64 {
            let _ = v;
        } else {
            assert!(v < (1u64 << bits));
        }
    }
    // bits=0 returns 0 but still consumes a squeeze.
    let mut t = Transcript::new_default(b"om/t");
    assert_eq!(t.challenge_index(b"i", 0), 0);
    assert_eq!(t.counter(), 1);
}

#[test]
#[should_panic(expected = "bits must be in 0..=64")]
fn index_bits_65_rejected() {
    Transcript::new_default(b"om/t").challenge_index(b"i", 65);
}

#[test]
fn index_rejected_call_consumes_nothing() {
    let mut t = Transcript::new_default(b"om/t");
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| t.challenge_index(b"i", 65)));
    assert!(r.is_err());
    assert_eq!(t.counter(), 0);
}

#[test]
fn sha384_state_width() {
    let mut t = Transcript::new(b"om/t", Hasher::sha384());
    assert_eq!(t.state().len(), 48);
    t.challenge_k(b"c");
}

#[test]
fn spec_28_known_answers() {
    // sha256 init state and outputs (spec 02 §2.8).
    let mut t = Transcript::new_default(b"om/test");
    assert_eq!(
        hex(t.state()),
        "094b8233cc2f99bca7fee328a3f2b29eb4bff8915e3eb5b3adf0bbe8206e9882"
    );
    let out = script(&mut t);
    assert_eq!(
        out[0],
        Value::String("4c85162be45b05c1f59f2b12a15c73dc".into())
    );
    assert_eq!(
        out[1],
        Value::String("5733c6c44ed9f94c5a1519ac574aa4c7".into())
    );
    assert_eq!(
        out[2],
        serde_json::json!([
            "f35bcd020b3cf51f3426741a833a144b",
            "967a1c72fbdd750ccf143c4dfa6a500c"
        ])
    );
    assert_eq!(
        out[3],
        Value::String("37410dd286009e56ddb0b277a12a7c6b".into())
    );
    assert_eq!(out[4], serde_json::json!(316459));
    assert_eq!(out[5], serde_json::json!(12779998978630712155u64));

    // sha3-256 init state (spec 02 §2.8).
    let t3 = Transcript::new(b"om/test", Hasher::sha3_256());
    assert_eq!(
        hex(t3.state()),
        "f31a8620eba31624f6a84d013f212c1440a4af3158b0711b5583034ecf324d12"
    );
}

#[test]
fn json_vector_conformance() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../reference/vectors/02-transcript/transcript.json");
    let text = std::fs::read_to_string(&path).expect("transcript.json exists");
    let doc: Value = serde_json::from_str(&text).unwrap();
    let vectors = doc["vectors"].as_array().expect("vectors array");
    assert_eq!(vectors.len(), 3);
    for v in vectors {
        let profile = v["profile"].as_str().unwrap();
        let hasher = Hasher::from_profile_id(profile.as_bytes()).unwrap();
        let label = v["protocol_label"].as_str().unwrap();
        let mut t = Transcript::new(label.as_bytes(), hasher);
        assert_eq!(
            hex(t.state()),
            v["init_state"].as_str().unwrap(),
            "init state, {profile}"
        );
        let got = script(&mut t);
        let want = v["outputs"].as_array().unwrap();
        assert_eq!(&got, want, "outputs, {profile}");
    }
}

#[test]
fn clone_is_independent() {
    let mut t = Transcript::new_default(b"om/test");
    t.absorb_bytes(b"a", b"1");
    let mut cloned = t.clone();
    assert_eq!(cloned.state(), t.state());
    assert_eq!(cloned.counter(), t.counter());
    // Same challenges from the clone point, then they diverge freely.
    assert_eq!(cloned.challenge_k(b"c"), t.challenge_k(b"c"));
    cloned.absorb_bytes(b"b", b"2");
    assert_ne!(cloned.challenge_k(b"c"), t.challenge_k(b"c"));
}

#[test]
fn absorb_resets_counter_and_challenge_ks_zero() {
    let mut t = Transcript::new_default(b"om/t");
    assert!(t.challenge_ks(b"x", 0).is_empty());
    assert_eq!(t.counter(), 0);
    t.challenge_k(b"x");
    t.challenge_k(b"x");
    assert_eq!(t.counter(), 2);
    t.absorb_ks(b"empty", &[]);
    assert_eq!(t.counter(), 0);
}

#[test]
fn absorb_ks_matches_concatenated_bytes() {
    let xs = [K::ONE, K::X, K::t(3)];
    let mut t1 = Transcript::new_default(b"om/t");
    t1.absorb_ks(b"ks", &xs);
    let mut data = Vec::new();
    for x in xs {
        data.extend_from_slice(&x.to_bytes());
    }
    let mut t2 = Transcript::new_default(b"om/t");
    t2.absorb_bytes(b"ks", &data);
    assert_eq!(t1.state(), t2.state());
    let mut t3 = Transcript::new_default(b"om/t");
    t3.absorb_k(b"k", xs[0]);
    let mut t4 = Transcript::new_default(b"om/t");
    t4.absorb_bytes(b"k", &xs[0].to_bytes());
    assert_eq!(t3.state(), t4.state());
}

// ---- label validation (spec 02 §2.7) ----

#[test]
#[should_panic(expected = "invalid transcript label")]
fn empty_protocol_label_rejected() {
    Transcript::new_default(b"");
}

#[test]
#[should_panic(expected = "invalid transcript label")]
fn space_in_label_rejected() {
    Transcript::new_default(b"om/test").absorb_bytes(b"a b", b"x");
}

#[test]
#[should_panic(expected = "invalid transcript label")]
fn control_in_label_rejected() {
    Transcript::new_default(b"om/test").challenge_k(b"a\x01b");
}

#[test]
#[should_panic(expected = "invalid transcript label")]
fn non_ascii_label_rejected() {
    Transcript::new_default(b"om/test").challenge_index(&[0xff], 8);
}

#[test]
#[should_panic(expected = "invalid transcript label")]
fn overlong_label_rejected() {
    Transcript::new_default(&[b'a'; 256]);
}

#[test]
fn boundary_labels_accepted() {
    let mut t = Transcript::new_default(&[b'a'; 255]);
    // Every printable byte 0x21..=0x7E.
    let all: Vec<u8> = (0x21u8..=0x7e).collect();
    t.absorb_bytes(&all, b"");
    t.challenge_k(b"pcs/fold");
    t.challenge_k(b"rs/sumcheck");
}

#[test]
fn enc_and_u64le() {
    assert_eq!(u64le(0), [0; 8]);
    assert_eq!(u64le(1), [1, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(u64le(u64::MAX), [0xff; 8]);
    assert_eq!(enc(b""), u64le(0).to_vec());
    let mut want = u64le(3).to_vec();
    want.extend_from_slice(b"abc");
    assert_eq!(enc(b"abc"), want);
}
