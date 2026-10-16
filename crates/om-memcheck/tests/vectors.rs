//! Byte-for-byte conformance against `reference/vectors/07-twist-shout/`
//! (the 07 parts of `reference/gen_vectors_07_08.py`, replayed in
//! Python by `test_vectors_07_08.py`). Every vector is re-proven and
//! compared field by field, and the stored proof is re-verified.

use std::path::PathBuf;

use om_field::K;
use om_memcheck::onehot::{
    AddrComps, EvalClaim, OneHotProof, VirtProof, comp_tables, onehot_aux, onehot_prove,
    onehot_verify,
};
use om_memcheck::shout::{ShoutClaims, ShoutParams, ShoutProof, shout_prove, shout_verify};
use om_memcheck::twist::{
    FinalMem, TwistClaims, TwistParams, TwistProof, build_witness, honest_claims, lt_eval,
    m0_table, twist_prove, twist_verify,
};
use om_sumcheck::{SumcheckProof, mle_eval_bits};
use om_transcript::Transcript;
use serde_json::Value;

fn load(name: &str) -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../reference/vectors/07-twist-shout")
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

fn kss(v: &Value) -> Vec<Vec<K>> {
    v.as_array().unwrap().iter().map(ks).collect()
}

fn us(v: &Value) -> Vec<usize> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_u64().unwrap() as usize)
        .collect()
}

fn uss(v: &Value) -> Vec<Vec<usize>> {
    v.as_array().unwrap().iter().map(us).collect()
}

fn words(v: &Value) -> Vec<u64> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_u64().unwrap())
        .collect()
}

fn u(v: &Value) -> usize {
    v.as_u64().unwrap() as usize
}

fn sc(v: &Value) -> SumcheckProof {
    SumcheckProof { round_msgs: kss(v) }
}

fn sc_opt(v: &Value) -> Option<SumcheckProof> {
    if v.is_null() { None } else { Some(sc(v)) }
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

fn assert_sc(proof: &SumcheckProof, v: &Value, what: &str) {
    let got: Vec<Vec<String>> = proof.round_msgs.iter().map(|m| hexes(m)).collect();
    let expect: Vec<Vec<String>> = v.as_array().unwrap().iter().map(stored_hexes).collect();
    assert_eq!(got, expect, "{what}");
}

fn assert_sc_opt(proof: &Option<SumcheckProof>, v: &Value, what: &str) {
    match (proof, v.is_null()) {
        (None, true) => {}
        (Some(p), false) => assert_sc(p, v, what),
        _ => panic!("{what}: presence mismatch"),
    }
}

fn assert_claims(claims: &[EvalClaim], v: &Value, what: &str) {
    let arr = v.as_array().unwrap();
    assert_eq!(claims.len(), arr.len(), "{what}: count");
    for (c, e) in claims.iter().zip(arr) {
        assert_eq!(c.poly, e["poly"].as_str().unwrap(), "{what}: poly");
        assert_eq!(
            hexes(&c.point),
            stored_hexes(&e["point"]),
            "{what}: {} point",
            c.poly
        );
        assert_eq!(
            c.value.to_hex(),
            e["value"].as_str().unwrap(),
            "{what}: {} value",
            c.poly
        );
    }
}

fn virt_proof(msgs: &Value, evals: &Value) -> Option<VirtProof> {
    if msgs.is_null() {
        None
    } else {
        Some(VirtProof {
            sc: sc(msgs),
            evals: ks(evals),
        })
    }
}

fn assert_virt(proof: &Option<VirtProof>, msgs: &Value, evals: &Value, what: &str) {
    match (proof, msgs.is_null()) {
        (None, true) => assert!(evals.is_null(), "{what}: evals"),
        (Some(p), false) => {
            assert_sc(&p.sc, msgs, what);
            assert_eq!(hexes(&p.evals), stored_hexes(evals), "{what}: evals");
        }
        _ => panic!("{what}: presence mismatch"),
    }
}

#[test]
fn lt_vectors() {
    let v = load("lt.json");
    for e in v.as_array().unwrap() {
        assert_eq!(lt_eval(&ks(&e["x"]), &ks(&e["y"])), k(&e["lt"]));
    }
}

#[test]
fn onehot_vector() {
    let v = load("onehot.json");
    let w = k(&v["cube_root_of_unity_c_zero"]["w"]);
    assert_eq!(K::ONE + w + w * w, K::ZERO);
    assert!(onehot_aux(&[w]).is_none());
    for e in v["aux"].as_array().unwrap() {
        let (rp, c) = onehot_aux(&ks(&e["r"])).unwrap();
        assert_eq!(hexes(&rp), stored_hexes(&e["r_prime"]));
        assert_eq!(c.to_hex(), e["C"].as_str().unwrap());
    }
    let inst = &v["instance"];
    let (ac, n) = (u(&inst["ac"]), u(&inst["n"]));
    let comps = AddrComps::from_usizes(&us(&inst["addrs"]), ac, 1);
    let dense = AddrComps::Bits {
        tables: comp_tables(&us(&inst["addrs"]), ac, 1),
        ac,
    };
    let names = vec!["A".to_string()];
    let proto = inst["protocol_label"].as_str().unwrap().as_bytes();
    let label = inst["label"].as_str().unwrap().as_bytes();
    let dense_out = onehot_prove(
        &[&dense],
        &names,
        ac,
        n,
        &mut Transcript::new_default(proto),
        label,
    );
    let (proof, claims) = onehot_prove(
        &[&comps],
        &names,
        ac,
        n,
        &mut Transcript::new_default(proto),
        label,
    );
    assert_sc(&proof.sc, &v["proof"]["round_msgs"], "onehot round_msgs");
    let got_evals: Vec<Vec<String>> = proof.evals.iter().map(|e| hexes(e)).collect();
    let exp_evals: Vec<Vec<String>> = v["proof"]["evals"]
        .as_array()
        .unwrap()
        .iter()
        .map(stored_hexes)
        .collect();
    assert_eq!(got_evals, exp_evals, "onehot evals");
    assert_claims(&claims, &v["claims"], "onehot claims");
    assert_eq!(dense_out, (proof.clone(), claims.clone()), "dense form");

    let stored = OneHotProof {
        sc: sc(&v["proof"]["round_msgs"]),
        evals: kss(&v["proof"]["evals"]),
    };
    let vclaims = onehot_verify(
        &names,
        ac,
        n,
        &stored,
        &mut Transcript::new_default(proto),
        label,
    )
    .unwrap();
    assert_claims(&vclaims, &v["claims"], "onehot verified claims");
}

fn shout_vector(name: &str) {
    let v = load(name);
    let p = &v["params"];
    let params = ShoutParams {
        name: p["name"].as_str().unwrap().to_string(),
        a: u(&p["a"]),
        d: u(&p["d"]),
        n: u(&p["n"]),
    };
    let table = kss(&v["table"]);
    let comps = AddrComps::from_usizes(&us(&v["addrs"]), params.a, params.d);
    let groups: Vec<ShoutClaims> = v["claim_groups"]
        .as_array()
        .unwrap()
        .iter()
        .map(|g| ShoutClaims {
            r_c: ks(&g["r_c"]),
            cols: us(&g["cols"]),
            rv: ks(&g["rv"]),
            bits: if g["bits"].is_null() {
                None
            } else {
                Some(ks(&g["bits"]))
            },
        })
        .collect();
    let proto = p["protocol_label"].as_str().unwrap().as_bytes();
    let label = p["label"].as_str().unwrap().as_bytes();
    let (proof, out) = shout_prove(
        &params,
        &table,
        &comps,
        &groups,
        &mut Transcript::new_default(proto),
        label,
    );
    let pr = &v["proof"];
    assert_sc(&proof.read, &pr["read"], "shout read");
    assert_eq!(
        hexes(&proof.ra_evals),
        stored_hexes(&pr["ra_evals"]),
        "shout ra_evals"
    );
    assert_virt(
        &proof.virt,
        &pr["virt_msgs"],
        &pr["virt_evals"],
        "shout virt",
    );
    assert_sc(&proof.onehot.sc, &pr["onehot_msgs"], "shout onehot");
    let got: Vec<Vec<String>> = proof.onehot.evals.iter().map(|e| hexes(e)).collect();
    let exp: Vec<Vec<String>> = pr["onehot_evals"]
        .as_array()
        .unwrap()
        .iter()
        .map(stored_hexes)
        .collect();
    assert_eq!(got, exp, "shout onehot evals");
    assert_claims(&out, &v["output_claims"], "shout output claims");

    let stored = ShoutProof {
        read: sc(&pr["read"]),
        ra_evals: ks(&pr["ra_evals"]),
        virt: virt_proof(&pr["virt_msgs"], &pr["virt_evals"]),
        onehot: OneHotProof {
            sc: sc(&pr["onehot_msgs"]),
            evals: kss(&pr["onehot_evals"]),
        },
    };
    let vout = shout_verify(
        &params,
        &table,
        &groups,
        &stored,
        &mut Transcript::new_default(proto),
        label,
    )
    .unwrap();
    assert_claims(&vout, &v["output_claims"], "shout verified claims");
}

#[test]
fn shout_d1_vector() {
    shout_vector("shout_d1.json");
}

#[test]
fn shout_d2_vector() {
    shout_vector("shout_d2.json");
}

fn twist_vector(name: &str) {
    let v = load(name);
    let p = &v["params"];
    let params = TwistParams {
        name: p["name"].as_str().unwrap().to_string(),
        a: u(&p["a"]),
        d: u(&p["d"]),
        p: u(&p["p"]),
        n: u(&p["n"]),
        ell: u(&p["ell"]),
    };
    let m0 = words(&v["m0"]);
    let (wit, info) = build_witness(
        &params,
        &m0,
        &uss(&v["reads"]),
        &us(&v["writes"]),
        &words(&v["new_words"]),
    );
    assert_eq!(info.final_state, words(&v["final_memory"]), "final memory");
    assert_eq!(info.inc, words(&v["inc"]), "inc words");
    let c = &v["claims"];
    let claims = TwistClaims {
        r_o: ks(&c["r_o"]),
        r_c: ks(&c["r_c"]),
        rv: ks(&c["rv"]),
        wv: k(&c["wv"]),
        bits: kss(&c["bits"]),
    };
    assert_eq!(
        honest_claims(&params, &info, &claims.r_o, &claims.r_c),
        claims,
        "honest claims"
    );
    let fin = if v["final_spec"].is_null() {
        None
    } else {
        let f = &v["final_spec"];
        Some(FinalMem {
            m: u(&f["m"]),
            s_out: u(&f["s_out"]),
            words: words(&f["words"]),
        })
    };
    let inc_extra = v["inc_extra"].as_bool().unwrap();
    let proto = p["protocol_label"].as_str().unwrap().as_bytes();
    let label = p["label"].as_str().unwrap().as_bytes();
    let (proof, out) = twist_prove(
        &params,
        &m0,
        &wit,
        &claims,
        &mut Transcript::new_default(proto),
        label,
        fin.as_ref(),
        inc_extra,
    );
    let pr = &v["proof"];
    assert_sc(&proof.rw, &pr["rw"], "twist rw");
    assert_eq!(
        hexes(&proof.rw_evals),
        stored_hexes(&pr["rw_evals"]),
        "twist rw_evals"
    );
    assert_sc(&proof.val, &pr["val"], "twist val");
    assert_eq!(
        hexes(&proof.val_evals),
        stored_hexes(&pr["val_evals"]),
        "twist val_evals"
    );
    assert_sc_opt(&proof.fin, &pr["fin"], "twist fin");
    match (&proof.fin_evals, pr["fin_evals"].is_null()) {
        (None, true) => {}
        (Some(e), false) => assert_eq!(hexes(e), stored_hexes(&pr["fin_evals"]), "twist fin_evals"),
        _ => panic!("twist fin_evals presence"),
    }
    match (proof.inc_extra, pr["inc_extra"].is_null()) {
        (None, true) => {}
        (Some(x), false) => assert_eq!(
            x.to_hex(),
            pr["inc_extra"].as_str().unwrap(),
            "twist inc_extra"
        ),
        _ => panic!("twist inc_extra presence"),
    }
    assert_virt(
        &proof.virt,
        &pr["virt_msgs"],
        &pr["virt_evals"],
        "twist virt",
    );
    assert_sc(&proof.onehot.sc, &pr["onehot_msgs"], "twist onehot");
    let got: Vec<Vec<String>> = proof.onehot.evals.iter().map(|e| hexes(e)).collect();
    let exp: Vec<Vec<String>> = pr["onehot_evals"]
        .as_array()
        .unwrap()
        .iter()
        .map(stored_hexes)
        .collect();
    assert_eq!(got, exp, "twist onehot evals");
    assert_claims(&out.claims, &v["output_claims"], "twist output claims");

    let stored = TwistProof {
        rw: sc(&pr["rw"]),
        rw_evals: ks(&pr["rw_evals"]),
        val: sc(&pr["val"]),
        val_evals: ks(&pr["val_evals"]),
        fin: sc_opt(&pr["fin"]),
        fin_evals: if pr["fin_evals"].is_null() {
            None
        } else {
            Some(ks(&pr["fin_evals"]))
        },
        inc_extra: if pr["inc_extra"].is_null() {
            None
        } else {
            Some(k(&pr["inc_extra"]))
        },
        virt: virt_proof(&pr["virt_msgs"], &pr["virt_evals"]),
        onehot: OneHotProof {
            sc: sc(&pr["onehot_msgs"]),
            evals: kss(&pr["onehot_evals"]),
        },
    };
    let m0t = m0_table(&m0, params.a, params.ell);
    let vout = twist_verify(
        &params,
        &|pt: &[K]| mle_eval_bits(&m0t, pt),
        &claims,
        &stored,
        &mut Transcript::new_default(proto),
        label,
        fin.as_ref(),
        inc_extra,
    )
    .unwrap();
    assert_claims(&vout.claims, &v["output_claims"], "twist verified claims");
}

#[test]
fn twist_reg_p2_d1_vector() {
    twist_vector("twist_reg_p2_d1.json");
}

#[test]
fn twist_reg_p2_d2_vector() {
    twist_vector("twist_reg_p2_d2.json");
}

#[test]
fn twist_ram_p1_d1_final_vector() {
    twist_vector("twist_ram_p1_d1_final.json");
}

#[test]
fn twist_ram_p1_d2_final_vector() {
    twist_vector("twist_ram_p1_d2_final.json");
}
