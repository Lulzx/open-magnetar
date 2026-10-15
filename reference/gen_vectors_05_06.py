"""Emit test vectors for sections 05 (Mosaic) and 06 (Spartan). Run from the reference/ directory:
    python3 gen_vectors_05_06.py
"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from openmagnetar import mosaic as M
from openmagnetar import spartan as S
from openmagnetar import toy_cpu as T
from openmagnetar.field import K
from openmagnetar.mle import mle_eval
from openmagnetar.transcript import Transcript

HERE = os.path.dirname(os.path.abspath(__file__))


def h(x):
    return x.hex()


def hs(xs):
    return [h(x) for x in xs]


def dump(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(obj, f, indent=1)
        f.write("\n")


def bits(v):
    return "".join(str(b) for b in v)


def mosaic_vectors():
    cases = []
    for comps, ell_min in (([(5, 3), (2, 4), (9, 3), (1, 0), (7, 1), (3, 4), (4, 2)], 0),
                           ([(1, 2)], 5), ([(10, 0), (11, 0), (12, 0)], 0), ([(3, 5), (1, 5), (2, 4)], 0)):
        lay = M.compute_layout(comps, ell_min)
        cases.append({"components": comps, "ell_min": ell_min, "ell": lay.ell,
                      "placements": [[p.comp_id, p.log_size, p.offset, p.suffix] for p in lay.placements]})
    dump(os.path.join(HERE, "vectors/05-mosaic/layout.json"), {"vectors": cases})

    rng = random.Random(0x0505)
    comps = [(5, 3), (2, 4), (9, 3), (1, 0), (7, 1), (3, 4), (4, 2)]
    lay = M.compute_layout(comps)
    tables = {cid: [rng.getrandbits(1) for _ in range(1 << ls)] for cid, ls in comps}
    G = M.build_G(lay, tables)
    claims = []
    for cid, ls in comps + [(2, 4)]:
        r = [K(rng.getrandbits(128)) for _ in range(ls)]
        claims.append(M.Claim(cid, r, mle_eval(tables[cid], r)))
    t = Transcript(b"vec-mosaic")
    proof, rG, vG = M.batch_prove(lay, claims, G, t)
    final = t.challenge_k(b"vec/final")
    dump(os.path.join(HERE, "vectors/05-mosaic/batch.json"), {"vectors": [{
        "protocol_label": "vec-mosaic", "ell": lay.ell,
        "tables": {str(cid): bits(tb) for cid, tb in tables.items()},
        "G": bits(G),
        "claims": [{"id": c.comp_id, "point": hs(c.point), "value": h(c.value)} for c in claims],
        "lifted_points": [hs(M.lift_point(lay, c)) for c in claims],
        "round_msgs": [hs(m) for m in proof.sumcheck.round_msgs],
        "v_G": h(vG), "r_G": hs(rG), "transcript_final": h(final)}]})


def spartan_vectors():
    rng = random.Random(0x0606)
    q = 4
    W, X, cross = T.witness(rng, q)
    rels, segs = T.structs(), T.segments()
    t = Transcript(b"vec-spartan")
    proof, claims = S.prove(rels, W, X, t, segments=segs, cross=cross)
    final = t.challenge_k(b"vec/final")
    tv = Transcript(b"vec-spartan")
    S.verify(rels, 2, X, proof, tv, segments=segs, cross=cross)
    assert tv.challenge_k(b"vec/final") == final
    dump(os.path.join(HERE, "vectors/06-spartan/virtual_spartan_toy.json"), {"vectors": [{
        "protocol_label": "vec-spartan", "prefix": "vsp", "q": q, "rho": T.RHO, "nu": T.NU,
        "W_rows": [bits(r) for r in W], "init": cross.init, "fin": cross.fin,
        "segments": [[s.seg_id, s.kind, s.log_cols, s.block] for s in segs],
        "cross_step": {"in_id": cross.in_id, "out_id": cross.out_id},
        "outer_msgs": {"bin": [hs(m) for m in proof.outer_msgs[0]], "fld": [hs(m) for m in proof.outer_msgs[1]]},
        "outer_finals": {"bin": hs(proof.outer_finals[0]), "fld": hs(proof.outer_finals[1])},
        "inner_msgs": [hs(m) for m in proof.inner.round_msgs],
        "v_W": h(proof.v_W), "seg_vals": hs(proof.seg_vals),
        "xs_msgs": [hs(m) for m in proof.xs_proof.round_msgs], "xs_vals": hs(proof.xs_vals),
        "claims": [{"id": c.comp_id, "point": hs(c.point), "value": h(c.value)} for c in claims],
        "transcript_final": h(final)}]})

    # single-relation SIMD Spartan (Construction 1 mode, whole-W claim)
    t = Transcript(b"vec-spartan1")
    p1, c1 = S.prove([rels[0]], W, X, t)
    final = t.challenge_k(b"vec/final")
    dump(os.path.join(HERE, "vectors/06-spartan/simd_spartan_bin.json"), {"vectors": [{
        "protocol_label": "vec-spartan1", "prefix": "vsp", "relation": "bin", "q": q,
        "W_rows": [bits(r) for r in W],
        "outer_msgs": [hs(m) for m in p1.outer_msgs[0]], "outer_finals": hs(p1.outer_finals[0]),
        "inner_msgs": [hs(m) for m in p1.inner.round_msgs], "v_W": h(p1.v_W),
        "claim": {"point": hs(c1[0].point), "value": h(c1[0].value)}, "transcript_final": h(final)}]})

    # next-MLE vectors
    nv = []
    for s in (1, 2, 3):
        a = [K(rng.getrandbits(128)) for _ in range(s)]
        b = [K(rng.getrandbits(128)) for _ in range(s)]
        nv.append({"s": s, "a": hs(a), "b": hs(b), "next": h(S.next_mle(a, b))})
    dump(os.path.join(HERE, "vectors/06-spartan/next_mle.json"), {"vectors": nv})


if __name__ == "__main__":
    mosaic_vectors()
    spartan_vectors()
    print("ok")
