import hashlib
import json
import os
import unittest

from openmagnetar import ligerito as lg
from openmagnetar import ntt
from openmagnetar.field import K
from openmagnetar.hashing import Hasher
from openmagnetar.merkle import MerkleTree
from openmagnetar.pcs import LigeritoPCS
from openmagnetar.transcript import Transcript

D = os.path.join(os.path.dirname(__file__), "..", "vectors", "04-pcs")


def load(n):
    with open(os.path.join(D, n)) as f:
        return json.load(f)


@unittest.skipUnless(os.path.isdir(D), "vectors not generated")
class TestVectors(unittest.TestCase):
    def test_merkle(self):
        for v in load("merkle.json")["vectors"]:
            leaves = [bytes.fromhex(x) for x in v["leaves"]]
            t = MerkleTree(Hasher(v["hash"]), leaves)
            self.assertEqual(t.root.hex(), v["root"])
            self.assertEqual([a.hex() for a in t.open(v["indices"])], v["auth"])

    def test_ntt(self):
        for v in load("ntt.json")["vectors"]:
            msg = [K.from_hex(x) for x in v["message"]]
            self.assertEqual([x.hex() for x in ntt.encode(msg, v["log_inv_rate"])], v["codeword"])

    def test_ligerito(self):
        for v in load("ligerito.json")["vectors"]:
            p = lg.LigeritoParams(v["n"], tuple(v["ks"]), tuple(v["rs"]), tuple(v["ts"]))
            pcs = LigeritoPCS(p)
            tab = [K.from_hex(x) for x in v["table"]]
            tr = Transcript(v["transcript_label"].encode())
            cm, st = pcs.commit(tab, tr)
            self.assertEqual(cm.root.hex(), v["root"])
            r = [K.from_hex(x) for x in v["point"]]
            y, pf = pcs.open(st, r, tr)
            self.assertEqual(y.hex(), v["value"])
            self.assertEqual(hashlib.sha256(pf.to_bytes()).hexdigest(), v["proof_bytes_sha256"])


if __name__ == "__main__":
    unittest.main()
