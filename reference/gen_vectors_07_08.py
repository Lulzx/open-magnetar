"""Emit test vectors for spec sections 07 (Twist/Shout/one-hot) and 08 (Router).

Usage: python3 reference/gen_vectors_07_08.py
"""

from __future__ import annotations

import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from openmagnetar.field import K, random_k
from openmagnetar.mle import mle_eval
from openmagnetar.onehot import (comp_tables, onehot_aux, onehot_prove, virt_prove,
                                 VirtGroup, VirtTerm)
from openmagnetar.router import (shift_R_eval, shift_prove, shift_witness, shift_valid,
                                 store_R_eval, store_prove, store_valid, store_witness)
from openmagnetar.shout import ShoutParams, shout_honest_claims, shout_prove
from openmagnetar.transcript import Transcript
from openmagnetar.twist import (FinalMem, TwistParams, build_witness, honest_claims, m0_table,
                                twist_prove, lt_eval)
from openmagnetar.onehot import bits_of

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "vectors")


def hx(x):
    if isinstance(x, K):
        return x.hex()
    if isinstance(x, (list, tuple)):
        return [hx(y) for y in x]
    if isinstance(x, dict):
        return {k: hx(v) for k, v in x.items()}
    return x


def claims_json(cl):
    return [{"poly": c.poly, "point": hx(c.point), "value": hx(c.value)} for c in cl]


def sc_json(sc):
    return None if sc is None else [hx(m) for m in sc.round_msgs]


def onehot_vec():
    rng = random.Random(701)
    aux = []
    for ac in (1, 3, 4):
        r = [random_k(rng) for _ in range(ac)]
        rp, C = onehot_aux(r)
        aux.append({"r": hx(r), "r_prime": hx(rp), "C": hx(C)})
    w = K.X ** (((1 << 128) - 1) // 3)
    n, ac = 3, 3
    addrs = [rng.randrange(1 << ac) for _ in range(1 << n)]
    comps = comp_tables(addrs, ac, 1)
    tr = Transcript(b"vec/07/onehot")
    proof, claims = onehot_prove(comps, ["A"], ac, n, tr, b"oh")
    return {"cube_root_of_unity_c_zero": {"w": hx(w)}, "aux": aux,
            "instance": {"ac": ac, "n": n, "addrs": addrs, "protocol_label": "vec/07/onehot",
                         "label": "oh"},
            "proof": {"round_msgs": sc_json(proof.sc), "evals": hx(proof.evals)},
            "claims": claims_json(claims)}


def shout_vec(a, d, n, c, seed):
    rng = random.Random(seed)
    NK, T = 1 << a, 1 << n
    table = [[random_k(rng) if h == 0 else K(rng.randint(0, 1)) for _ in range(NK)]
             for h in range(c)]
    addrs = [rng.randrange(NK) for _ in range(T)]
    comps = comp_tables(addrs, a, d)
    r_c = [random_k(rng) for _ in range(n)]
    p = ShoutParams("sh", a, d, n)
    r_c2 = [random_k(rng) for _ in range(n)]
    groups = [shout_honest_claims(p, table, comps, r_c),
              shout_honest_claims(p, table, comps, r_c2, cols=[0], with_bits=False)]
    tr = Transcript(b"vec/07/shout")
    proof, out = shout_prove(p, table, comps, groups, tr, b"S")
    return {"params": {"a": a, "d": d, "n": n, "c": c, "protocol_label": "vec/07/shout",
                       "label": "S", "name": "sh"},
            "table": hx(table), "addrs": addrs,
            "claim_groups": [{"r_c": hx(c.r_c), "cols": c.cols, "rv": hx(c.rv),
                              "bits": None if c.bits is None else hx(c.bits)} for c in groups],
            "proof": {"read": sc_json(proof.read), "ra_evals": hx(proof.ra_evals),
                      "virt_msgs": sc_json(proof.virt.sc) if proof.virt else None,
                      "virt_evals": hx(proof.virt.evals) if proof.virt else None,
                      "onehot_msgs": sc_json(proof.onehot.sc),
                      "onehot_evals": hx(proof.onehot.evals)},
            "output_claims": claims_json(out)}


def twist_vec(a, d, p, n, ell, seed, final=None, inc_extra=False):
    rng = random.Random(seed)
    NK, T, L = 1 << a, 1 << n, 1 << ell
    m0 = [rng.getrandbits(L) if rng.random() < 0.5 else 0 for _ in range(NK)]
    reads = [[rng.randrange(NK) for _ in range(T)] for _ in range(p)]
    writes = [rng.randrange(NK) for _ in range(T)]
    new = [rng.getrandbits(L) for _ in range(T)]
    params = TwistParams("tw", a, d, p, n, ell)
    wit, info = build_witness(params, m0, reads, writes, new)
    r_o = [random_k(rng) for _ in range(ell)]
    r_c = [random_k(rng) for _ in range(n)]
    claims = honest_claims(params, info, r_o, r_c)
    fin = None
    if final:
        m, s_out = final
        fin = FinalMem(m, s_out, [info["final"][(s_out << m) + i] for i in range(1 << m)])
    tr = Transcript(b"vec/07/twist")
    proof, out = twist_prove(params, m0, wit, claims, tr, b"T", fin, inc_extra)
    d_ = {"params": {"a": a, "d": d, "p": p, "n": n, "ell": ell, "name": "tw",
                     "protocol_label": "vec/07/twist", "label": "T"},
          "m0": m0, "reads": reads, "writes": writes, "new_words": new,
          "final_memory": info["final"], "inc": info["inc"],
          "claims": {"r_o": hx(r_o), "r_c": hx(r_c), "rv": hx(claims.rv), "wv": hx(claims.wv),
                     "bits": hx(claims.bits)},
          "final_spec": None if fin is None else {"m": fin.m, "s_out": fin.s_out,
                                                  "words": fin.words},
          "inc_extra": inc_extra,
          "proof": {"rw": sc_json(proof.rw), "rw_evals": hx(proof.rw_evals),
                    "val": sc_json(proof.val), "val_evals": hx(proof.val_evals),
                    "fin": sc_json(proof.fin), "fin_evals": hx(proof.fin_evals),
                    "inc_extra": hx(proof.inc_extra) if proof.inc_extra else None,
                    "virt_msgs": sc_json(proof.virt.sc) if proof.virt else None,
                    "virt_evals": hx(proof.virt.evals) if proof.virt else None,
                    "onehot_msgs": sc_json(proof.onehot.sc),
                    "onehot_evals": hx(proof.onehot.evals)},
          "output_claims": claims_json(out.claims)}
    return d_


def lt_vec():
    rng = random.Random(702)
    out = []
    for n in (1, 3, 5):
        x = [random_k(rng) for _ in range(n)]
        y = [random_k(rng) for _ in range(n)]
        out.append({"x": hx(x), "y": hx(y), "lt": hx(lt_eval(x, y))})
    return out


def shift_vec(n, wb, seed):
    rng = random.Random(seed)
    W, T = 1 << wb, 1 << n
    cycles = []
    for j in range(T):
        src = rng.getrandbits(W)
        if j == 1:
            cycles.append((src, None))
            continue
        while True:
            kind, amt = rng.randrange(8), rng.randrange(W)
            if shift_valid(kind, amt, wb):
                break
        cycles.append((src, (amt, kind)))
    wit = shift_witness(cycles, wb)
    r_o = [random_k(rng) for _ in range(wb)]
    r_j = [random_k(rng) for _ in range(n)]
    y = mle_eval(wit["Y"], r_o + r_j)
    tr = Transcript(b"vec/08/shift")
    proof, claims = shift_prove(n, wit, r_o, r_j, y, tr, b"sh", wb)
    return {"params": {"n": n, "wbits": wb, "protocol_label": "vec/08/shift", "label": "sh"},
            "cycles": [[s, None if r is None else {"amt": r[0], "kind": r[1]}] for s, r in cycles],
            "claim": {"r_o": hx(r_o), "r_j": hx(r_j), "y": hx(y)},
            "proof": {"round_msgs": sc_json(proof.sc), "evals": hx(proof.evals)},
            "output_claims": claims_json(claims)}


def store_vec(n, wb, seed):
    rng = random.Random(seed)
    W, T = 1 << wb, 1 << n
    cycles = []
    for j in range(T):
        old, src = rng.getrandbits(W), rng.getrandbits(W)
        if j == 1:
            cycles.append((old, src, None))
            continue
        while True:
            h, a = rng.randrange(4), rng.randrange(W // 8)
            if store_valid(h, a, wb):
                break
        cycles.append((old, src, (h, a)))
    wit = store_witness(cycles, wb)
    r_o = [random_k(rng) for _ in range(wb)]
    r_j = [random_k(rng) for _ in range(n)]
    y = mle_eval(wit["Inc"], r_o + r_j)
    tr = Transcript(b"vec/08/store")
    proof, claims = store_prove(n, wit, r_o, r_j, y, tr, b"st", wb)
    return {"params": {"n": n, "wbits": wb, "protocol_label": "vec/08/store", "label": "st"},
            "cycles": [[o, s, None if r is None else {"width": r[0], "offset": r[1]}]
                       for o, s, r in cycles],
            "claim": {"r_o": hx(r_o), "r_j": hx(r_j), "y": hx(y)},
            "proof": {"round_msgs": sc_json(proof.sc), "evals": hx(proof.evals)},
            "output_claims": claims_json(claims)}


def R_vec():
    rng = random.Random(703)
    sh, st = [], []
    for _ in range(3):
        r_o = [random_k(rng) for _ in range(6)]
        r_u = [random_k(rng) for _ in range(6)]
        r_h = [random_k(rng) for _ in range(9)]
        sh.append({"r_o": hx(r_o), "r_u": hx(r_u), "r_h": hx(r_h),
                   "value": hx(shift_R_eval(r_o, r_u, r_h, 6))})
        r_u = [random_k(rng) for _ in range(7)]
        r_h = [random_k(rng) for _ in range(2)]
        r_a = [random_k(rng) for _ in range(3)]
        st.append({"r_o": hx(r_o), "r_u": hx(r_u), "r_h": hx(r_h), "r_a": hx(r_a),
                   "value": hx(store_R_eval(r_o, r_u, r_h, r_a, 6))})
    return {"R_sh": sh, "R_st": st}


def generate():
    v07 = {
        "onehot.json": onehot_vec(),
        "lt.json": lt_vec(),
        "shout_d1.json": shout_vec(3, 1, 3, 2, 711),
        "shout_d2.json": shout_vec(4, 2, 3, 3, 712),
        "twist_reg_p2_d1.json": twist_vec(3, 1, 2, 3, 6, 721),
        "twist_reg_p2_d2.json": twist_vec(4, 2, 2, 3, 6, 722, inc_extra=True),
        "twist_ram_p1_d1_final.json": twist_vec(3, 1, 1, 3, 6, 723, final=(2, 1), inc_extra=True),
        "twist_ram_p1_d2_final.json": twist_vec(4, 2, 1, 3, 6, 724, final=(2, 3), inc_extra=True),
    }
    v08 = {
        "R_eval_wb6.json": R_vec(),
        "shift_wb3.json": shift_vec(2, 3, 801),
        "store_wb4.json": store_vec(2, 4, 802),
        "store_wb6.json": store_vec(1, 6, 803),
        "shift_wb6.json": shift_vec(1, 6, 804),
    }
    return {"07-twist-shout": v07, "08-router": v08}


def main():
    for sect, files in generate().items():
        d = os.path.join(OUT, sect)
        os.makedirs(d, exist_ok=True)
        for name, obj in files.items():
            with open(os.path.join(d, name), "w") as f:
                json.dump(obj, f, indent=1, sort_keys=True)
                f.write("\n")
            print("wrote", sect, name)


if __name__ == "__main__":
    main()
