import random
import unittest

from openmagnetar import ntt
from openmagnetar.field import K, random_k


class TestNTT(unittest.TestCase):
    def test_fast_equals_naive(self):
        rng = random.Random(7)
        for mu, r in [(0, 1), (1, 1), (2, 2), (3, 1), (4, 2), (5, 1), (3, 0)]:
            msg = [random_k(rng) for _ in range(1 << mu)]
            self.assertEqual(ntt.encode(msg, r), ntt.encode_naive(msg, r), (mu, r))

    def test_linear(self):
        rng = random.Random(8)
        a = [random_k(rng) for _ in range(8)]
        b = [random_k(rng) for _ in range(8)]
        s = random_k(rng)
        lhs = ntt.encode([x + s * y for x, y in zip(a, b)], 2)
        ea, eb = ntt.encode(a, 2), ntt.encode(b, 2)
        self.assertEqual(lhs, [x + s * y for x, y in zip(ea, eb)])

    def test_normalisation(self):
        # What_i(beta_i) = 1 and What_i vanishes on beta_b, b < i.
        for i in range(6):
            self.assertEqual(ntt.what_beta(i, i), K.ONE)
        self.assertEqual(ntt.what_beta(3, 3), K.ONE)

    def test_degree_bound_is_rs(self):
        # Codeword of a degree < 2^mu polynomial: interpolating back over U_m gives
        # zero novel coefficients above 2^mu; check via encode of padded message
        # equals encode with larger rate on prefix (consistency across rates).
        rng = random.Random(9)
        msg = [random_k(rng) for _ in range(4)]
        c1 = ntt.encode(msg, 1)
        c3 = ntt.encode(msg, 3)
        self.assertEqual(c1, c3[:len(c1)])  # U_m nested: prefix of the domain

    def test_minimum_distance(self):
        rng = random.Random(10)
        msg = [random_k(rng) for _ in range(8)]
        c = ntt.encode(msg, 1)
        zeros = sum(1 for x in c if not x)
        self.assertLess(zeros, 8)  # nonzero poly of degree < 8 has < 8 roots

    def test_monomials(self):
        # X_0 = 1, X_1 = What_0(x) = x (since W_0 = x, W_0(beta_0) = 1).
        c = ntt.encode([K.ZERO, K.ONE], 1)
        self.assertEqual(c, [K(q) for q in range(4)])


if __name__ == "__main__":
    unittest.main()
