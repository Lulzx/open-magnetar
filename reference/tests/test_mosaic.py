import copy
import random
import unittest

from openmagnetar import mosaic as M
from openmagnetar.field import K, random_k
from openmagnetar.mle import mle_eval
from openmagnetar.sumcheck import VerificationError
from openmagnetar.transcript import Transcript

R = random.Random(77)
COMPS = [(5, 3), (2, 4), (9, 3), (1, 0), (7, 1), (3, 4), (4, 2)]


def setup(ell_min=0):
    lay = M.compute_layout(COMPS, ell_min)
    tables = {cid: [R.getrandbits(1) for _ in range(1 << ls)] for cid, ls in COMPS}
    return lay, tables, M.build_G(lay, tables)


class TestLayout(unittest.TestCase):
    def test_order_alignment_disjoint(self):
        lay, _, _ = setup()
        self.assertEqual([p.comp_id for p in lay.placements], [2, 3, 5, 9, 4, 7, 1])
        total = sum(1 << ls for _, ls in COMPS)       # 16+16+8+8+4+2+1 = 55
        self.assertEqual(lay.ell, 6)
        self.assertGreaterEqual(1 << lay.ell, total)
        end = 0
        for p in lay.placements:
            self.assertEqual(p.offset % (1 << p.log_size), 0)
            self.assertEqual(p.offset, end)
            self.assertEqual(p.suffix, p.offset >> p.log_size)
            end += 1 << p.log_size

    def test_ell_min_and_order_independence(self):
        a = M.compute_layout(COMPS, 9)
        b = M.compute_layout(list(reversed(COMPS)), 9)
        self.assertEqual(a, b)
        self.assertEqual(a.ell, 9)

    def test_single_and_duplicates(self):
        self.assertEqual(M.compute_layout([(1, 0)]).ell, 0)
        with self.assertRaises(ValueError):
            M.compute_layout([(1, 2), (1, 3)])

    def test_lifting_eq4(self):
        lay, tables, G = setup()
        for cid, ls in COMPS:
            r = [random_k(R) for _ in range(ls)]
            c = M.Claim(cid, r, mle_eval(tables[cid], r))
            self.assertEqual(mle_eval(G, M.lift_point(lay, c)), c.value)


class TestBatching(unittest.TestCase):
    def claims(self, lay, tables):
        out = []
        for cid, ls in COMPS + [(2, 4), (2, 4)]:    # component 2 gets three claims
            r = [random_k(R) for _ in range(ls)]
            out.append(M.Claim(cid, r, mle_eval(tables[cid], r)))
        return out

    def test_completeness(self):
        lay, tables, G = setup()
        cl = self.claims(lay, tables)
        proof, rG, vG = M.batch_prove(lay, cl, G, Transcript(b"m"))
        rG2, vG2 = M.batch_verify(lay, cl, proof, Transcript(b"m"))
        self.assertEqual((rG, vG), (rG2, vG2))
        self.assertEqual(mle_eval(G, rG), vG)

    def test_negative(self):
        lay, tables, G = setup()
        cl = self.claims(lay, tables)
        proof, _, _ = M.batch_prove(lay, cl, G, Transcript(b"m"))
        p2 = copy.deepcopy(proof)
        p2.sumcheck.round_msgs[2][0] = p2.sumcheck.round_msgs[2][0] + K.ONE
        with self.assertRaises(VerificationError):
            M.batch_verify(lay, cl, p2, Transcript(b"m"))
        p2 = copy.deepcopy(proof)
        p2.v_G = p2.v_G + K.ONE
        with self.assertRaises(VerificationError):
            M.batch_verify(lay, cl, p2, Transcript(b"m"))
        cl2 = list(cl)
        cl2[3] = M.Claim(cl[3].comp_id, cl[3].point, cl[3].value + K.ONE)
        with self.assertRaises(VerificationError):
            M.batch_verify(lay, cl2, proof, Transcript(b"m"))
        with self.assertRaises(VerificationError):
            M.batch_verify(lay, [M.Claim(1234, [], K.ZERO)], proof, Transcript(b"m"))
        with self.assertRaises(VerificationError):
            M.batch_verify(lay, [M.Claim(2, [K.ONE], K.ZERO)], proof, Transcript(b"m"))

    def test_false_claim_not_provable(self):
        lay, tables, G = setup()
        cl = self.claims(lay, tables)
        cl[0] = M.Claim(cl[0].comp_id, cl[0].point, cl[0].value + K.ONE)
        with self.assertRaises(ValueError):
            M.batch_prove(lay, cl, G, Transcript(b"m"))


if __name__ == "__main__":
    unittest.main()
