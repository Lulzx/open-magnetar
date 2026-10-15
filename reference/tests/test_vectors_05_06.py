import json
import os
import unittest

from openmagnetar import mosaic as M
from openmagnetar import spartan as S
from openmagnetar import toy_cpu as T
from openmagnetar.field import K
from openmagnetar.sumcheck import SumcheckProof
from openmagnetar.transcript import Transcript

V = os.path.join(os.path.dirname(__file__), "..", "vectors")


def load(p):
    with open(os.path.join(V, p)) as f:
        return json.load(f)["vectors"]


def ks(xs):
    return [K.from_hex(x) for x in xs]


class TestVectors(unittest.TestCase):
    def test_layout(self):
        for v in load("05-mosaic/layout.json"):
            lay = M.compute_layout([tuple(c) for c in v["components"]], v["ell_min"])
            self.assertEqual(lay.ell, v["ell"])
            self.assertEqual([[p.comp_id, p.log_size, p.offset, p.suffix] for p in lay.placements], v["placements"])

    def test_batch_replay(self):
        for v in load("05-mosaic/batch.json"):
            lay = M.compute_layout([(int(k), len(t).bit_length() - 1) for k, t in v["tables"].items()])
            claims = [M.Claim(c["id"], ks(c["point"]), K.from_hex(c["value"])) for c in v["claims"]]
            proof = M.BatchProof(SumcheckProof([ks(m) for m in v["round_msgs"]]), K.from_hex(v["v_G"]))
            t = Transcript(v["protocol_label"].encode())
            rG, vG = M.batch_verify(lay, claims, proof, t)
            self.assertEqual(hs := [x.hex() for x in rG], v["r_G"])
            self.assertEqual(t.challenge_k(b"vec/final").hex(), v["transcript_final"])

    def test_vsp_replay(self):
        v = load("06-spartan/virtual_spartan_toy.json")[0]
        segs = [S.Segment(*s) for s in v["segments"]]
        cross = S.CrossStep(v["cross_step"]["in_id"], v["cross_step"]["out_id"], v["init"], v["fin"])
        proof = S.SpartanProof(
            [[ks(m) for m in v["outer_msgs"][n]] for n in ("bin", "fld")],
            [ks(v["outer_finals"][n]) for n in ("bin", "fld")],
            SumcheckProof([ks(m) for m in v["inner_msgs"]]), K.from_hex(v["v_W"]), ks(v["seg_vals"]),
            SumcheckProof([ks(m) for m in v["xs_msgs"]]), ks(v["xs_vals"]))
        t = Transcript(v["protocol_label"].encode())
        out = S.verify(T.structs(), 2, [[] for _ in range(v["q"])], proof, t, segments=segs, cross=cross)
        self.assertEqual([c.value.hex() for c in out], [c["value"] for c in v["claims"]])
        self.assertEqual(t.challenge_k(b"vec/final").hex(), v["transcript_final"])


if __name__ == "__main__":
    unittest.main()
