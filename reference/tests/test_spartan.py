import copy
import random
import unittest

from openmagnetar import spartan as S
from openmagnetar import toy_cpu as T
from openmagnetar.field import K, random_k
from openmagnetar.mle import eq_table, mle_eval
from openmagnetar.r1cs import R1CS, SparseMatrix, build_z, flatten_W, simd_satisfied
from openmagnetar.sumcheck import VerificationError
from openmagnetar.transcript import Transcript

R = random.Random(2024)


def fresh(label=b"test"):
    return Transcript(label)


class TestR1CS(unittest.TestCase):
    def test_mle_matches_bruteforce(self):
        M = SparseMatrix(2, 3, {(0, 1): K(5), (3, 7): K(9), (2, 2): K(1)})
        rr = [random_k(R) for _ in range(2)]
        rc = [random_k(R) for _ in range(3)]
        dense = [K.ZERO] * 32
        for (r, c), v in M.entries.items():
            dense[r + 4 * c] = v
        self.assertEqual(M.mle(rr, rc), mle_eval(dense, rr + rc))
        ft = M.fold_rows(rr)
        self.assertEqual(mle_eval(ft, rc), M.mle(rr, rc))

    def test_mul_vec_bits_vs_k(self):
        M = SparseMatrix(2, 3, {(0, 1): K(5), (0, 2): K(7), (3, 7): K(9)})
        z = [0, 1, 1, 0, 0, 0, 0, 1]
        self.assertEqual(M.mul_vec(z), M.mul_vec([K(b) for b in z]))
        self.assertEqual(M.mul_vec(z)[0], K(5) + K(7))

    def test_toy_satisfied_and_not(self):
        rels = T.structs()
        W, X, _ = T.witness(R, 4)
        self.assertTrue(simd_satisfied(rels, W, X))
        W[2][T.OUT] ^= 1
        self.assertFalse(simd_satisfied(rels, W, X))
        W, X, _ = T.witness(R, 4)
        W[1][T.YC + 1] ^= 1
        self.assertFalse(simd_satisfied(rels, W, X))

    def test_next_mle(self):
        for s in range(0, 4):
            a = [random_k(R) for _ in range(s)]
            b = [random_k(R) for _ in range(s)]
            n = 1 << s
            tbl = [K.ZERO] * (n * n)
            for i in range(n - 1):
                tbl[i + n * (i + 1)] = K.ONE
            self.assertEqual(S.next_mle(a, b), mle_eval(tbl, a + b))


def _public_input_rels():
    # nu=3: z = (w0..w3, 1, x0, 0, 0). Row 0: w0 * w1 = x0 ; row 1: (w2 + w3) * 1 = w0.
    a = {(0, 0): 1, (1, 2): 1, (1, 3): 1}
    b = {(0, 1): 1, (1, 4): 1}
    c = {(0, 5): 1, (1, 0): 1}
    return R1CS("B", 1, 3, SparseMatrix(1, 3, a), SparseMatrix(1, 3, b), SparseMatrix(1, 3, c))


class TestSingleSpartan(unittest.TestCase):
    def _run(self, rels, W, X, q):
        s = q.bit_length() - 1
        proof, claims = S.prove(rels, W, X, fresh())
        out = S.verify(rels, s, X, proof, fresh())
        self.assertEqual(len(out), 1)
        self.assertEqual(claims[0].value, out[0].value)
        pt = list(out[0].point)
        self.assertEqual(mle_eval(flatten_W(W), pt), out[0].value)
        return proof

    def test_bin_only_simd(self):
        W, X, _ = T.witness(R, 4)
        self._run([T.structs()[0]], W, X, 4)

    def test_fld_only(self):
        W, X, _ = T.witness(R, 2)
        self._run([T.structs()[1]], W, X, 2)

    def test_single_instance(self):
        W, X, _ = T.witness(R, 1)
        self._run([T.structs()[0]], W, X, 1)

    def test_public_inputs(self):
        rel = _public_input_rels()
        W, X = [], []
        for _ in range(4):
            w0, w1 = R.getrandbits(1), R.getrandbits(1)
            w3 = R.getrandbits(1)
            w2 = w0 ^ w3
            W.append([w0, w1, w2, w3])
            X.append([w0 & w1])
        self.assertTrue(simd_satisfied([rel], W, X))
        self._run([rel], W, X, 4)
        # wrong public input: verifier rejects the honest proof
        proof, _ = S.prove([rel], W, X, fresh())
        X2 = copy.deepcopy(X)
        X2[1][0] ^= 1
        with self.assertRaises(VerificationError):
            S.verify([rel], 2, X2, proof, fresh())

    def test_unsatisfied(self):
        rels = [T.structs()[0]]
        W, X, _ = T.witness(R, 4)
        W[3][T.OUT + 2] ^= 1
        with self.assertRaises(ValueError):
            S.prove(rels, W, X, fresh())
        proof, _ = S.prove(rels, W, X, fresh(), unchecked=True)
        with self.assertRaises(VerificationError):
            S.verify(rels, 2, X, proof, fresh())

    def test_tamper(self):
        rels = [T.structs()[0]]
        W, X, _ = T.witness(R, 4)
        proof, _ = S.prove(rels, W, X, fresh())
        for mut in (lambda p: p.outer_msgs[0][1].__setitem__(0, p.outer_msgs[0][1][0] + K.ONE),
                    lambda p: p.outer_finals[0].__setitem__(2, p.outer_finals[0][2] + K.ONE),
                    lambda p: p.inner.round_msgs[2].__setitem__(1, p.inner.round_msgs[2][1] + K.ONE)):
            p2 = copy.deepcopy(proof)
            mut(p2)
            with self.assertRaises(VerificationError):
                S.verify(rels, 2, X, p2, fresh())
        p2 = copy.deepcopy(proof)
        p2.v_W = p2.v_W + K.ONE
        with self.assertRaises(VerificationError):
            S.verify(rels, 2, X, p2, fresh())


class TestVirtualSpartan(unittest.TestCase):
    def setUp(self):
        self.rels = T.structs()
        self.segs = T.segments()
        self.W, self.X, self.cross = T.witness(R, 4)

    def prove(self, **kw):
        return S.prove(self.rels, self.W, self.X, fresh(), segments=self.segs, cross=self.cross, **kw)

    def verify(self, proof, cross=None, X=None, segs=None):
        return S.verify(self.rels, 2, X or self.X, proof, fresh(), segments=segs or self.segs,
                        cross=cross or self.cross)

    def test_completeness_and_claims(self):
        proof, claims = self.prove()
        out = self.verify(proof)
        self.assertEqual([(c.comp_id, c.point, c.value) for c in claims], [(c.comp_id, c.point, c.value) for c in out])
        # 6 non-pad... 7 non-pad segments + 2 cross-step claims; S_in and S_out have two claims each
        self.assertEqual(len(out), 9)
        by = {s.seg_id: s for s in self.segs}
        for c in out:
            tbl = S._segment_table(self.W, by[c.comp_id])
            self.assertEqual(mle_eval(tbl, list(c.point)), c.value)
        pts = [c.point for c in out if c.comp_id == T.SEG_IN]
        self.assertEqual(len(pts), 2)
        self.assertNotEqual(pts[0], pts[1])

    def test_shared_instance_challenges_separate_row(self):
        # Re-derive the point from the claims: all non-cross claims share the instance suffix.
        proof, claims = self.prove()
        suffixes = {tuple(c.point[len(c.point) - 2:]) for c in claims[:7]}
        self.assertEqual(len(suffixes), 1)

    def test_other_sizes(self):
        for q in (1, 2, 8):
            W, X, cross = T.witness(R, q)
            proof, claims = S.prove(self.rels, W, X, fresh(), segments=self.segs, cross=cross)
            S.verify(self.rels, q.bit_length() - 1, X, proof, fresh(), segments=self.segs, cross=cross)

    def test_nonzero_init(self):
        W, X, cross = T.witness(R, 4, init=9)
        proof, _ = S.prove(self.rels, W, X, fresh(), segments=self.segs, cross=cross)
        S.verify(self.rels, 2, X, proof, fresh(), segments=self.segs, cross=cross)

    def test_unsatisfied_constraint(self):
        self.W[1][T.CARRY + 1] ^= 1
        with self.assertRaises(ValueError):
            self.prove()
        proof, _ = self.prove(unchecked=True)
        with self.assertRaises(VerificationError):
            self.verify(proof)

    def test_unsatisfied_fld_constraint(self):
        self.W[2][T.YC] ^= 1
        with self.assertRaises(ValueError):
            self.prove()
        proof, _ = self.prove(unchecked=True)
        with self.assertRaises(VerificationError):
            self.verify(proof)

    def test_inconsistent_cross_step(self):
        # every row satisfies both relations, but IN[j] != OUT[j-1] for j = 2
        rows = [T.witness(R, 1, init=v)[0][0] for v in (0, 0, 7, 0)]
        W = rows
        # make row 1 -> row 2 inconsistent: row 1 outputs (0 + a) , row 2 starts at 7
        out_prev = sum(W[1][T.OUT + i] << i for i in range(4))
        if out_prev == 7:
            W[2] = T.witness(R, 1, init=6)[0][0]
        X = self.X
        self.assertTrue(simd_satisfied(self.rels, W, X))
        cross = S.CrossStep(T.SEG_IN, T.SEG_OUT, [0] * 4, [W[3][T.OUT + i] for i in range(4)])
        with self.assertRaises(ValueError):
            S.prove(self.rels, W, X, fresh(), segments=self.segs, cross=cross)
        proof, _ = S.prove(self.rels, W, X, fresh(), segments=self.segs, cross=cross, unchecked=True)
        with self.assertRaises(VerificationError):
            S.verify(self.rels, 2, X, proof, fresh(), segments=self.segs, cross=cross)

    def test_wrong_public_boundary(self):
        proof, _ = self.prove()
        bad_init = S.CrossStep(T.SEG_IN, T.SEG_OUT, [1, 0, 0, 0], self.cross.fin)
        with self.assertRaises(VerificationError):
            self.verify(proof, cross=bad_init)
        fin = list(self.cross.fin)
        fin[2] ^= 1
        with self.assertRaises(VerificationError):
            self.verify(proof, cross=S.CrossStep(T.SEG_IN, T.SEG_OUT, self.cross.init, fin))

    def test_tampered_segment_claim(self):
        proof, _ = self.prove()
        for i in range(len(proof.seg_vals)):
            p2 = copy.deepcopy(proof)
            p2.seg_vals[i] = p2.seg_vals[i] + K.ONE
            with self.assertRaises(VerificationError):
                self.verify(p2)

    def test_tampered_other_fields(self):
        proof, _ = self.prove()
        muts = [
            lambda p: p.outer_msgs[1][4].__setitem__(1, p.outer_msgs[1][4][1] + K.ONE),   # fld instance round
            lambda p: p.outer_msgs[0][0].__setitem__(2, p.outer_msgs[0][0][2] + K.ONE),   # bin row round
            lambda p: p.outer_finals[1].__setitem__(0, p.outer_finals[1][0] + K.ONE),
            lambda p: p.inner.round_msgs[0].__setitem__(0, p.inner.round_msgs[0][0] + K.ONE),
            lambda p: setattr(p, "v_W", p.v_W + K.ONE),
            lambda p: p.xs_vals.__setitem__(0, p.xs_vals[0] + K.ONE),
            lambda p: p.xs_vals.__setitem__(1, p.xs_vals[1] + K.ONE),
            lambda p: p.xs_proof.round_msgs[1].__setitem__(0, p.xs_proof.round_msgs[1][0] + K.ONE),
        ]
        for m in muts:
            p2 = copy.deepcopy(proof)
            m(p2)
            with self.assertRaises(VerificationError):
                self.verify(p2)

    def test_nonzero_padding_rejected(self):
        self.W[1][28] = 1   # a padding column (segment SEG_PAD); no constraint touches it
        proof, _ = self.prove()
        with self.assertRaises(VerificationError):
            self.verify(proof)
        self.W[1][28] = 0
        self.W[1][26] = 1   # an implicitly uncovered column
        proof, _ = self.prove()
        with self.assertRaises(VerificationError):
            self.verify(proof)

    def test_bad_layout_rejected(self):
        bad = self.segs + [S.Segment(99, "direct", 2, 0)]
        with self.assertRaises(ValueError):
            S.check_layout(bad, T.NU)


if __name__ == "__main__":
    unittest.main()
