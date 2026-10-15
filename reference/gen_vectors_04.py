"""Emit JSON test vectors for spec section 04 into reference/vectors/04-pcs/."""

import hashlib
import json
import os

from openmagnetar import ligerito as lg
from openmagnetar import ntt
from openmagnetar import ring_switch as rsw
from openmagnetar.field import K
from openmagnetar.hashing import Hasher
from openmagnetar.merkle import MerkleTree
from openmagnetar.mle import mle_eval
from openmagnetar.pcs import BitPCS, LigeritoPCS
from openmagnetar.transcript import Transcript

OUT = os.path.join(os.path.dirname(__file__), "vectors", "04-pcs")


class Det:
    """Deterministic byte source: SHA-256 in counter mode."""

    def __init__(self, seed: bytes):
        self.seed, self.c = seed, 0

    def k(self) -> K:
        self.c += 1
        return K.from_bytes(hashlib.sha256(self.seed + self.c.to_bytes(8, "little")).digest()[:16])

    def bit(self) -> int:
        self.c += 1
        return hashlib.sha256(self.seed + self.c.to_bytes(8, "little")).digest()[0] & 1


def hx(xs):
    return [x.hex() for x in xs]


def write(name, obj):
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, name), "w") as f:
        json.dump(obj, f, indent=1)
        f.write("\n")


def merkle_vectors():
    out = []
    for prof in ("sha256", "sha3-256"):
        h = Hasher(prof)
        for n, idx in ((1, [0]), (5, [1, 4]), (8, [0, 1, 6]), (11, [2, 3, 10])):
            leaves = [bytes([i, 7]) * (1 + i % 3) for i in range(n)]
            t = MerkleTree(h, leaves)
            out.append(dict(hash=prof, leaves=[x.hex() for x in leaves], indices=idx,
                            root=t.root.hex(), auth=[a.hex() for a in t.open(idx)]))
    write("merkle.json", dict(vectors=out))


def ntt_vectors():
    d = Det(b"ntt")
    out = []
    for mu, r in ((0, 1), (2, 1), (3, 2), (4, 1)):
        msg = [d.k() for _ in range(1 << mu)]
        out.append(dict(log_msg=mu, log_inv_rate=r, message=hx(msg), codeword=hx(ntt.encode(msg, r))))
    write("ntt.json", dict(
        what_beta=[[ntt.what_beta(i, b).hex() for b in range(i, 6)] for i in range(6)],
        vectors=out))


def ring_vectors():
    d = Det(b"rs")
    ell = 9
    bits = [d.bit() for _ in range(1 << ell)]
    r = [d.k() for _ in range(ell)]
    y = mle_eval(bits, r)
    proof, r_s, v = rsw.rs_prove(bits, r, y, Transcript(b"om/test/rs"))
    write("ring_switch.json", dict(
        ell=ell, bits=bytes(sum(bits[8 * i + j] << j for j in range(8)) for i in range(len(bits) // 8)).hex(),
        point=hx(r), value=y.hex(), packed=hx(rsw.pack(bits)), s=hx(proof.s),
        sumcheck_msgs=[hx(m) for m in proof.sumcheck.round_msgs], r_s=hx(r_s), v=v.hex(),
        transcript_label="om/test/rs"))


def ligerito_vectors():
    d = Det(b"lg")
    out = []
    for p in (lg.LigeritoParams(8, (3,), (1,), (5,)), lg.LigeritoParams(10, (3, 3), (1, 2), (6, 5))):
        pcs = LigeritoPCS(p)
        tab = [d.k() for _ in range(1 << p.n)]
        tr = Transcript(b"om/test/ligerito")
        cm, st = pcs.commit(tab, tr)
        r = [d.k() for _ in range(p.n)]
        y, pf = pcs.open(st, r, tr)
        out.append(dict(n=p.n, ks=list(p.ks), rs=list(p.rs), ts=list(p.ts), table=hx(tab),
                        root=cm.root.hex(), point=hx(r), value=y.hex(),
                        next_roots=[x.hex() for x in pf.roots],
                        final=hx(pf.final), proof_bytes_sha256=hashlib.sha256(pf.to_bytes()).hexdigest(),
                        proof_len=len(pf.to_bytes()), transcript_label="om/test/ligerito"))
    write("ligerito.json", dict(vectors=out))


if __name__ == "__main__":
    merkle_vectors()
    ntt_vectors()
    ring_vectors()
    ligerito_vectors()
    print("wrote", OUT)
