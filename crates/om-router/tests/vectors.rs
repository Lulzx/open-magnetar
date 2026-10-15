//! Byte-for-byte conformance against `reference/vectors/08-router/`
//! (the 08 parts of `reference/gen_vectors_07_08.py`, replayed in
//! Python by `test_vectors_07_08.py`). Every vector is re-proven and
//! compared field by field, and the stored proof is re-verified; the
//! fast provers must reproduce the same stored proof too.

use std::path::PathBuf;

use om_field::K;
use om_memcheck::onehot::EvalClaim;
use om_router::router::{
    RouterProof, ShiftCycle, StoreCycle, shift_prove, shift_prove_fast, shift_r_eval, shift_verify,
    shift_witness, store_prove, store_prove_fast, store_r_eval, store_verify, store_witness,
};
use om_sumcheck::{SumcheckProof, mle_eval_bits};
use om_transcript::Transcript;
use serde_json::Value;

fn load(name: &str) -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../reference/vectors/08-router")
        .join(name);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    serde_json::from_str(&text).unwrap()
}

fn k(v: &Value) -> K {
    K::from_hex(v.as_str().unwrap()).unwrap()
}

fn ks(v: &Value) -> Vec<K> {
    v.as_array().unwrap().iter().map(k).collect()
}

fn u(v: &Value) -> usize {
    v.as_u64().unwrap() as usize
}

fn word(v: &Value) -> u64 {
    v.as_u64().unwrap()
}

fn hexes(xs: &[K]) -> Vec<String> {
    xs.iter().map(|x| x.to_hex()).collect()
}

fn stored_hexes(v: &Value) -> Vec<String> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_str().unwrap().to_string())
        .collect()
}

fn assert_proof(proof: &RouterProof, v: &Value, what: &str) {
    let got: Vec<Vec<String>> = proof.sc.round_msgs.iter().map(|m| hexes(m)).collect();
    let expect: Vec<Vec<String>> = v["round_msgs"]
        .as_array()
        .unwrap()
        .iter()
        .map(stored_hexes)
        .collect();
    assert_eq!(got, expect, "{what}: round_msgs");
    assert_eq!(
        hexes(&proof.evals),
        stored_hexes(&v["evals"]),
        "{what}: evals"
    );
}

fn assert_claims(claims: &[EvalClaim], v: &Value, what: &str) {
    let arr = v.as_array().unwrap();
    assert_eq!(claims.len(), arr.len(), "{what}: claim count");
    for (c, cv) in claims.iter().zip(arr) {
        assert_eq!(c.poly, cv["poly"].as_str().unwrap(), "{what}: poly");
        assert_eq!(
            hexes(&c.point),
            stored_hexes(&cv["point"]),
            "{what}: point of {}",
            c.poly
        );
        assert_eq!(
            c.value.to_hex(),
            cv["value"].as_str().unwrap(),
            "{what}: value of {}",
            c.poly
        );
    }
}

fn stored_proof(v: &Value) -> RouterProof {
    RouterProof {
        sc: SumcheckProof {
            round_msgs: v["round_msgs"].as_array().unwrap().iter().map(ks).collect(),
        },
        evals: ks(&v["evals"]),
    }
}

fn shift_vector(name: &str) {
    let v = load(name);
    let (n, wb) = (u(&v["params"]["n"]), u(&v["params"]["wbits"]));
    let proto = v["params"]["protocol_label"].as_str().unwrap().as_bytes();
    let label = v["params"]["label"].as_str().unwrap().as_bytes();
    let cycles: Vec<ShiftCycle> = v["cycles"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            let route = if c[1].is_null() {
                None
            } else {
                Some((u(&c[1]["amt"]), u(&c[1]["kind"])))
            };
            (word(&c[0]), route)
        })
        .collect();
    let wit = shift_witness(&cycles, wb);
    let r_o = ks(&v["claim"]["r_o"]);
    let r_j = ks(&v["claim"]["r_j"]);
    let y = k(&v["claim"]["y"]);
    // the stored y is the MLE of the witness output at r_o || r_j
    assert_eq!(mle_eval_bits(&wit.y, &[&r_o[..], &r_j[..]].concat()), y);

    let (proof, claims) = shift_prove(
        n,
        &wit,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(proto),
        label,
        wb,
    );
    assert_proof(&proof, &v["proof"], name);
    assert_claims(&claims, &v["output_claims"], name);

    let (fast, fast_claims) = shift_prove_fast(
        n,
        &wit,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(proto),
        label,
        wb,
    );
    assert_proof(&fast, &v["proof"], name);
    assert_claims(&fast_claims, &v["output_claims"], name);

    let stored = stored_proof(&v["proof"]);
    let vc = shift_verify(
        n,
        &r_o,
        &r_j,
        y,
        &stored,
        &mut Transcript::new_default(proto),
        label,
        wb,
    )
    .unwrap();
    assert_claims(&vc, &v["output_claims"], name);
}

fn store_vector(name: &str) {
    let v = load(name);
    let (n, wb) = (u(&v["params"]["n"]), u(&v["params"]["wbits"]));
    let proto = v["params"]["protocol_label"].as_str().unwrap().as_bytes();
    let label = v["params"]["label"].as_str().unwrap().as_bytes();
    let cycles: Vec<StoreCycle> = v["cycles"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            let route = if c[2].is_null() {
                None
            } else {
                Some((u(&c[2]["width"]), u(&c[2]["offset"])))
            };
            (word(&c[0]), word(&c[1]), route)
        })
        .collect();
    let wit = store_witness(&cycles, wb);
    let r_o = ks(&v["claim"]["r_o"]);
    let r_j = ks(&v["claim"]["r_j"]);
    let y = k(&v["claim"]["y"]);
    assert_eq!(mle_eval_bits(&wit.inc, &[&r_o[..], &r_j[..]].concat()), y);

    let (proof, claims) = store_prove(
        n,
        &wit,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(proto),
        label,
        wb,
    );
    assert_proof(&proof, &v["proof"], name);
    assert_claims(&claims, &v["output_claims"], name);

    let (fast, fast_claims) = store_prove_fast(
        n,
        &wit,
        &r_o,
        &r_j,
        y,
        &mut Transcript::new_default(proto),
        label,
        wb,
    );
    assert_proof(&fast, &v["proof"], name);
    assert_claims(&fast_claims, &v["output_claims"], name);

    let stored = stored_proof(&v["proof"]);
    let vc = store_verify(
        n,
        &r_o,
        &r_j,
        y,
        &stored,
        &mut Transcript::new_default(proto),
        label,
        wb,
    )
    .unwrap();
    assert_claims(&vc, &v["output_claims"], name);
}

#[test]
fn vector_r_eval_wb6() {
    let v = load("R_eval_wb6.json");
    for case in v["R_sh"].as_array().unwrap() {
        assert_eq!(
            shift_r_eval(&ks(&case["r_o"]), &ks(&case["r_u"]), &ks(&case["r_h"]), 6),
            k(&case["value"])
        );
    }
    for case in v["R_st"].as_array().unwrap() {
        assert_eq!(
            store_r_eval(
                &ks(&case["r_o"]),
                &ks(&case["r_u"]),
                &ks(&case["r_h"]),
                &ks(&case["r_a"]),
                6
            ),
            k(&case["value"])
        );
    }
}

#[test]
fn vector_shift_wb3() {
    shift_vector("shift_wb3.json");
}

#[test]
fn vector_shift_wb6() {
    shift_vector("shift_wb6.json");
}

#[test]
fn vector_store_wb4() {
    store_vector("store_wb4.json");
}

#[test]
fn vector_store_wb6() {
    store_vector("store_wb6.json");
}
