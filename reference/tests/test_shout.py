import random
import unittest

from openmagnetar.field import K, random_k
from openmagnetar.mle import mle_eval
from openmagnetar.onehot import comp_tables
from openmagnetar.shout import (ShoutClaims, ShoutParams, shout_honest_claims, shout_prove,
                                shout_verify)
from openmagnetar.sumcheck import VerificationError
from openmagnetar.transcript import Transcript


def tr():
    return Transcript(b"test/shout")


def make(a, d, n, c, seed):
    rng = random.Random(seed)
    NK, T = 1 << a, 1 << n
    table = [[random_k(rng) if h == 0 else K(rng.randint(0, 1)) for _ in range(NK)]
             for h in range(c)]
    addrs = [rng.randrange(NK) for _ in range(T)]
    comps = comp_tables(addrs, a, d)
    r_c = [random_k(rng) for _ in range(n)]
    p = ShoutParams("sh", a, d, n)
    return p, table, addrs, comps, r_c


class ShoutTest(unittest.TestCase):
    def check_cfg(self, a, d, n, c, seed):
        p, table, addrs, comps, r_c = make(a, d, n, c, seed)
        claims = shout_honest_claims(p, table, comps, r_c)
        # honest claims agree with the direct definition
        for h in range(c):
            self.assertEqual(claims.rv[h],
                             mle_eval([table[h][ad] for ad in addrs], r_c))
        proof, oc = shout_prove(p, table, comps, [claims], tr(), b"S")
        vc = shout_verify(p, table, [claims], proof, tr(), b"S")
        self.assertEqual([(x.poly, x.point, x.value) for x in oc],
                         [(x.poly, x.point, x.value) for x in vc])
        for x in vc:
            i = int(x.poly.split("/")[-1]) - 1
            self.assertEqual(mle_eval(comps[i], x.point), x.value)
        return p, table, comps, claims, proof

    def test_d1(self):
        self.check_cfg(3, 1, 3, 2, 1)

    def test_d2(self):
        self.check_cfg(4, 2, 3, 3, 2)

    def test_d3(self):
        self.check_cfg(6, 3, 2, 1, 3)

    def test_multi_point_groups(self):
        # three claim groups at different cycle points, different column subsets,
        # one without address-bit claims (bytecode usage: Spartan, Twist, Router claims)
        for a, d in ((4, 2), (3, 1)):
            p, table, addrs, comps, r_c = make(a, d, 3, 3, 9)
            rng = random.Random(10)
            pts = [[random_k(rng) for _ in range(3)] for _ in range(3)]
            groups = [shout_honest_claims(p, table, comps, pts[0]),
                      shout_honest_claims(p, table, comps, pts[1], cols=[1]),
                      shout_honest_claims(p, table, comps, pts[2], cols=[0, 2], with_bits=False)]
            proof, oc = shout_prove(p, table, comps, groups, tr(), b"S")
            vc = shout_verify(p, table, groups, proof, tr(), b"S")
            self.assertEqual([(x.poly, x.point, x.value) for x in oc],
                             [(x.poly, x.point, x.value) for x in vc])
            for x in vc:
                i = int(x.poly.split("/")[-1]) - 1
                self.assertEqual(mle_eval(comps[i], x.point), x.value)
            bad = list(groups)
            bad[1] = ShoutClaims(groups[1].r_c, [1], [groups[1].rv[0] + K.ONE], groups[1].bits)
            with self.assertRaises(VerificationError):
                shout_verify(p, table, bad, proof, tr(), b"S")

    def test_wrong_value(self):
        p, table, comps, claims, proof = self.check_cfg(4, 2, 3, 2, 4)
        bad = ShoutClaims(claims.r_c, claims.cols, [claims.rv[0] + K.ONE, claims.rv[1]],
                          claims.bits)
        with self.assertRaises(VerificationError):
            shout_verify(p, table, [bad], proof, tr(), b"S")

    def test_wrong_address_bit(self):
        p, table, comps, claims, proof = self.check_cfg(4, 2, 3, 2, 5)
        bits = list(claims.bits)
        bits[2] = bits[2] + K.ONE
        with self.assertRaises(VerificationError):
            shout_verify(p, table, [ShoutClaims(claims.r_c, claims.cols, claims.rv, bits)],
                         proof, tr(), b"S")

    def test_hamming_two(self):
        p, table, addrs, comps, r_c = make(4, 2, 3, 2, 6)
        comps[0][1 + 4 * 2] = 1
        comps[0][2 + 4 * 2] = 1
        # honest claims for the *claimed* (unique-address) lookups
        good = comp_tables(addrs, 4, 2)
        claims = shout_honest_claims(p, table, good, r_c)
        proof, _ = shout_prove(p, table, comps, [claims], tr(), b"S")
        with self.assertRaises(VerificationError):
            shout_verify(p, table, [claims], proof, tr(), b"S")

    def test_hamming_zero(self):
        p, table, addrs, comps, r_c = make(4, 2, 3, 2, 7)
        for u in range(4):
            comps[1][u + 4 * 3] = 0   # row j = 3 of component 2 is all-zero
        good = comp_tables(addrs, 4, 2)
        claims = shout_honest_claims(p, table, good, r_c)
        proof, _ = shout_prove(p, table, comps, [claims], tr(), b"S")
        with self.assertRaises(VerificationError):
            shout_verify(p, table, [claims], proof, tr(), b"S")

    def test_hamming_zero_d1(self):
        p, table, addrs, comps, r_c = make(3, 1, 3, 1, 8)
        for u in range(8):
            comps[0][u + 8 * 5] = 0
        good = comp_tables(addrs, 3, 1)
        claims = shout_honest_claims(p, table, good, r_c)
        proof, _ = shout_prove(p, table, comps, [claims], tr(), b"S")
        with self.assertRaises(VerificationError):
            shout_verify(p, table, [claims], proof, tr(), b"S")


if __name__ == "__main__":
    unittest.main()
