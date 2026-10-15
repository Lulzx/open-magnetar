import random
import unittest

from openmagnetar.field import K, random_k
from openmagnetar.mle import eq_table, mle_eval
from openmagnetar.sumcheck import (SumcheckProof, VerificationError, batch_claims,
                                   batched_combine, interpolate_eval, sumcheck_prove,
                                   sumcheck_verify)
from openmagnetar.transcript import Transcript

COMBINES = {
    1: (1, lambda v: v[0]),
    2: (2, lambda v: v[0] * v[1]),
    3: (3, lambda v: v[0] * v[1] * v[2]),
}


def setup(d, m, seed):
    rng = random.Random(seed)
    n, f = COMBINES[d]
    tables = [[random_k(rng) for _ in range(1 << m)] for _ in range(n)]
    claim = K.ZERO
    for i in range(1 << m):
        claim = claim + f([T[i] for T in tables])
    return tables, f, claim


class SumcheckTest(unittest.TestCase):
    def run_pv(self, d, m, seed=1):
        tables, f, claim = setup(d, m, seed)
        pt = Transcript(b"om/sc")
        proof, rs, evals = sumcheck_prove(claim, tables, f, d, pt, b"sc/round")
        vt = Transcript(b"om/sc")
        r, exp = sumcheck_verify(claim, m, d, proof, vt, b"sc/round")
        return tables, f, claim, proof, rs, evals, r, exp

    def test_completeness(self):
        for d in (1, 2, 3):
            for m in (0, 1, 2, 5):
                tables, f, claim, proof, rs, evals, r, exp = self.run_pv(d, m)
                self.assertEqual(r, rs)
                self.assertEqual(exp, f(evals))
                self.assertEqual(evals, [mle_eval(T, r) for T in tables])
                self.assertTrue(all(len(x) == d for x in proof.round_msgs))

    def test_bit_tables(self):
        rng = random.Random(9)
        t = [rng.getrandbits(1) for _ in range(16)]
        f = lambda v: v[0] * v[0]
        claim = K.ZERO
        for x in t:
            claim = claim + K(x)
        proof, rs, ev = sumcheck_prove(claim, [t], f, 2, Transcript(b"x"), b"s")
        r, exp = sumcheck_verify(claim, 4, 2, proof, Transcript(b"x"), b"s")
        self.assertEqual(exp, f(ev))

    def test_tampered_message(self):
        tables, f, claim, proof, rs, evals, r, exp = self.run_pv(2, 4)
        bad = SumcheckProof([list(m) for m in proof.round_msgs])
        bad.round_msgs[1][0] = bad.round_msgs[1][0] + K.ONE
        r2, exp2 = sumcheck_verify(claim, 4, 2, bad, Transcript(b"om/sc"), b"sc/round")
        self.assertNotEqual(exp2, f(evals))
        with self.assertRaises(VerificationError):
            sumcheck_verify(claim, 4, 2, SumcheckProof(proof.round_msgs[:-1]), Transcript(b"om/sc"), b"sc/round")
        short = SumcheckProof([m[:-1] if i == 0 else m for i, m in enumerate(proof.round_msgs)])
        with self.assertRaises(VerificationError):
            sumcheck_verify(claim, 4, 2, short, Transcript(b"om/sc"), b"sc/round")

    def test_wrong_claim(self):
        tables, f, claim = setup(3, 4, 2)
        with self.assertRaises(ValueError):
            sumcheck_prove(claim + K.ONE, tables, f, 3, Transcript(b"om/sc"), b"s")
        proof, rs, evals = sumcheck_prove(claim, tables, f, 3, Transcript(b"om/sc"), b"s")
        r, exp = sumcheck_verify(claim + K.ONE, 4, 3, proof, Transcript(b"om/sc"), b"s")
        self.assertNotEqual(exp, f(evals))

    def test_interpolate(self):
        rng = random.Random(7)
        c = [random_k(rng) for _ in range(4)]
        p = lambda x: c[0] + c[1] * x + c[2] * x * x + c[3] * x * x * x
        ys = [p(K.t(k)) for k in range(4)]
        z = random_k(rng)
        self.assertEqual(interpolate_eval(ys, z), p(z))

    def test_eq_sumcheck(self):
        # sum_b eq(tau,b) * a(b) * b(b) == claim; degree 3
        rng = random.Random(11)
        m = 4
        tau = [random_k(rng) for _ in range(m)]
        a = [rng.getrandbits(1) for _ in range(1 << m)]
        b = [rng.getrandbits(1) for _ in range(1 << m)]
        e = eq_table(tau)
        f = lambda v: v[0] * v[1] * v[2]
        claim = K.ZERO
        for i in range(1 << m):
            claim = claim + f([e[i], K(a[i]), K(b[i])])
        proof, rs, ev = sumcheck_prove(claim, [e, a, b], f, 3, Transcript(b"x"), b"s")
        _, exp = sumcheck_verify(claim, m, 3, proof, Transcript(b"x"), b"s")
        self.assertEqual(exp, f(ev))
        from openmagnetar.mle import eq_eval
        self.assertEqual(ev[0], eq_eval(tau, rs))

    def test_batching(self):
        m = 3
        t1, f1, c1 = setup(2, m, 21)
        t2, f2, c2 = setup(3, m, 22)
        pt = Transcript(b"x")
        coeffs, comb = batch_claims([c1, c2], pt, b"b")
        f = batched_combine(coeffs, [f1, f2], [2, 3])
        proof, rs, ev = sumcheck_prove(comb, t1 + t2, f, 3, pt, b"s")
        vt = Transcript(b"x")
        coeffs_v, comb_v = batch_claims([c1, c2], vt, b"b")
        self.assertEqual(comb, comb_v)
        r, exp = sumcheck_verify(comb_v, m, 3, proof, vt, b"s")
        self.assertEqual(exp, batched_combine(coeffs_v, [f1, f2], [2, 3])(ev))
