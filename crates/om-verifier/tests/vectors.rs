//! Stored-vector gate: the Python-generated proof in
//! `reference/vectors/11-12/fib_ligerito_test.json` verifies
//! directly (Python `TestVectors.test_replay_vector`).

use std::path::PathBuf;

use om_format::{decode_instance, decode_proof, decode_vk};
use om_prover::Derived;
use om_verifier::{verify, verify_strict};
use serde_json::Value;

fn hex_bytes(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd hex");
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex digit"))
        .collect()
}

fn to_hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn replay_stored_python_vector() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../reference/vectors/11-12/fib_ligerito_test.json");
    let v: Value =
        serde_json::from_slice(&std::fs::read(&path).expect("read vector")).expect("parse vector");

    let vk = decode_vk(&hex_bytes(v["vk_hex"].as_str().expect("vk_hex"))).expect("decode vk");
    assert_eq!(
        to_hex(&vk.digest()),
        v["vk_digest"].as_str().expect("vk_digest")
    );
    let inst = decode_instance(&hex_bytes(
        v["instance_hex"].as_str().expect("instance_hex"),
    ))
    .expect("decode instance");
    let blob = hex_bytes(v["proof_hex"].as_str().expect("proof_hex"));

    // The stored Python proof verifies as a blob...
    assert!(verify(&vk, &inst, blob.as_slice().into()));
    // ...and decoded into memory via om-format.
    let derived = Derived::new(&vk);
    let di = derived.instance(inst.t).expect("instance derivation");
    let proof = decode_proof(&vk, &blob, inst.t, &derived.proof_shape(&di)).expect("decode proof");
    assert!(verify_strict(&vk, &inst, &proof).is_ok());
    // A tampered copy of the stored proof rejects.
    let mut bad = blob.clone();
    let last = bad.len() - 1;
    bad[last] ^= 1;
    assert!(!verify(&vk, &inst, bad.as_slice().into()));
}
