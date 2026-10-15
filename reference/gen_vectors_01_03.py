"""Emit JSON vectors for sections 01-03. Run from the repo root:
python3 reference/gen_vectors_01_03.py"""
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from openmagnetar.field import K, random_k  # noqa: E402
from openmagnetar.hashing import Hasher  # noqa: E402
from openmagnetar.mle import eq_table, mle_eval  # noqa: E402
from openmagnetar.sumcheck import sumcheck_prove, sumcheck_verify  # noqa: E402
from openmagnetar.transcript import Transcript  # noqa: E402

sys.path.insert(0, os.path.join(HERE, "tests"))
from test_transcript import script  # noqa: E402


def dump(sub, name, obj):
    d = os.path.join(HERE, "vectors", sub)
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, name), "w") as f:
        json.dump(obj, f, indent=1)
        f.write("\n")


def transcript_vectors():
    vs = []
    for prof in ("sha256", "sha3-256", "sha384"):
        t = Transcript(b"om/test", Hasher(prof))
        init_state = t.state.hex()
        vs.append({"profile": prof, "protocol_label": "om/test", "init_state": init_state,
                   "script": "absorb_bytes(test/bytes,'hello'); absorb_k(test/k,K(0x0123456789ABCDEF)); "
                             "absorb_ks(test/ks,[1,X,X+1]); challenge_k(test/c1) x2; challenge_ks(test/cs,2); "
                             "challenge_nonzero_k(test/nz); challenge_index(test/idx,20); challenge_index(test/idx64,64)",
                   "outputs": script(Transcript(b"om/test", Hasher(prof)))})
    dump("02-transcript", "transcript.json", {"vectors": vs})


COMB = {1: (1, lambda v: v[0]), 2: (2, lambda v: v[0] * v[1]), 3: (3, lambda v: v[0] * v[1] * v[2])}
DESC = {1: "g = T0", 2: "g = T0*T1", 3: "g = T0*T1*T2"}


def sumcheck_vectors():
    vs = []
    for d in (1, 2, 3):
        m = 3
        rng = random.Random(1000 + d)
        n, f = COMB[d]
        tables = [[random_k(rng) for _ in range(1 << m)] for _ in range(n)]
        claim = K.ZERO
        for i in range(1 << m):
            claim = claim + f([T[i] for T in tables])
        proof, rs, ev = sumcheck_prove(claim, tables, f, d, Transcript(b"om/sc"), b"sc/round")
        r, exp = sumcheck_verify(claim, m, d, proof, Transcript(b"om/sc"), b"sc/round")
        assert r == rs and exp == f(ev)
        vs.append({"degree": d, "num_vars": m, "summand": DESC[d], "protocol_label": "om/sc",
                   "label": "sc/round", "tables": [[x.hex() for x in T] for T in tables],
                   "claim": claim.hex(), "round_msgs": [[x.hex() for x in msg] for msg in proof.round_msgs],
                   "challenges": [x.hex() for x in rs], "table_evals": [x.hex() for x in ev],
                   "final_claim": exp.hex()})
    dump("03-sumcheck", "sumcheck.json", {"vectors": vs})
    rng = random.Random(77)
    r = [random_k(rng) for _ in range(3)]
    tab = [random_k(rng) for _ in range(8)]
    dump("03-sumcheck", "mle.json", {
        "r": [x.hex() for x in r], "eq_table": [x.hex() for x in eq_table(r)],
        "table": [x.hex() for x in tab], "mle_eval": mle_eval(tab, r).hex()})


if __name__ == "__main__":
    transcript_vectors()
    sumcheck_vectors()
    print("ok")
