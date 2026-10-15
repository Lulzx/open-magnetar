import random
import unittest

from openmagnetar.field import K, random_k
from openmagnetar.mle import eq_eval, eq_table, mle_eval
from openmagnetar.onehot import (comp_tables, full_table, onehot_aux, onehot_prove,
                                 onehot_verify, sample_onehot_point, split_addr, virt_prove,
                                 virt_verify, VirtGroup, VirtTerm)
from openmagnetar.sumcheck import VerificationError
from openmagnetar.transcript import Transcript


def tr():
    return Transcript(b"test/onehot")


class AddressTest(unittest.TestCase):
    def test_chunks_low_first(self):
        self.assertEqual(split_addr(0b110101, 6, 2), [0b101, 0b110])
        self.assertEqual(split_addr(0b110101, 6, 3), [0b01, 0b01, 0b11])

    def test_full_table_is_product(self):
        a, d = 4, 2
        addrs = [3, 12, 0, 15]
        comps = comp_tables(addrs, a, d)
        full = full_table(comps, a, d, 4)
        for j, ad in enumerate(addrs):
            for k in range(16):
                self.assertEqual(full[k + 16 * j], int(k == ad))


class FrobeniusIdentityTest(unittest.TestCase):
    def test_eq_cubed(self):
        # eq(r,u)^3 = C(r) eq(r',u) for Boolean u (characteristic 2)
        rng = random.Random(7)
        for ac in (1, 2, 3, 4):
            r = [random_k(rng) for _ in range(ac)]
            aux = onehot_aux(r)
            self.assertIsNotNone(aux)
            rp, C = aux
            for u in range(1 << ac):
                ub = [K((u >> i) & 1) for i in range(ac)]
                lhs = eq_eval(r, ub) ** 3
                self.assertEqual(lhs, C * eq_eval(rp, ub))

    def test_delta_star_formula(self):
        # Delta*(j; r) = A~(r)^3 + C A~(r') equals the collision polynomial
        # A~(r) A~(r^2) + sum_u A(u) eq(r,u) eq(r^2,u) for bit rows.
        rng = random.Random(8)
        ac = 3
        for _ in range(20):
            row = [rng.randint(0, 1) for _ in range(1 << ac)]
            r = [random_k(rng) for _ in range(ac)]
            rp, C = onehot_aux(r)
            s = [x * x for x in r]
            At = mle_eval(row, r)
            delta = At * mle_eval(row, s) + sum(
                (eq_table(r)[u] * eq_table(s)[u] for u in range(1 << ac) if row[u]), K.ZERO)
            star = At ** 3 + C * mle_eval(row, rp)
            self.assertEqual(delta, star)
            self.assertEqual(mle_eval(row, s), At * At)   # Frobenius
            if sum(row) <= 1:
                self.assertEqual(star, K.ZERO)
            else:
                self.assertNotEqual(star, K.ZERO)

    def test_zero_c_detected(self):
        # primitive cube root of unity in GF(4) inside GF(2^128): c = 1 + w + w^2 = 0
        w = K.X ** (((1 << 128) - 1) // 3)
        self.assertEqual(K.ONE + w + w * w, K.ZERO)
        self.assertIsNone(onehot_aux([K.ONE, w]))
        self.assertIsNotNone(onehot_aux([K.ONE, K.X]))


class OneHotProtocolTest(unittest.TestCase):
    def run_check(self, comps, ac, n):
        names = [f"c{i}" for i in range(len(comps))]
        t1, t2 = tr(), tr()
        proof, claims = onehot_prove(comps, names, ac, n, t1, b"oh")
        vclaims = onehot_verify(names, ac, n, proof, t2, b"oh")
        return comps, claims, vclaims

    def test_honest(self):
        rng = random.Random(3)
        n, ac = 3, 3
        addrs = [[rng.randrange(8) for _ in range(8)] for _ in range(3)]
        comps = [comp_tables(ad, 3, 1)[0] for ad in addrs]
        _, claims, vclaims = self.run_check(comps, ac, n)
        for c, v in zip(claims, vclaims):
            self.assertEqual((c.poly, c.point, c.value), (v.poly, v.point, v.value))
            idx = int(c.poly[1:])
            self.assertEqual(mle_eval(comps[idx], c.point), c.value)

    def test_hamming_weight_two_rejected(self):
        n, ac = 2, 3
        comps = [comp_tables([1, 2, 3, 4], 3, 1)[0]]
        comps[0][5 + 8 * 2] = 1      # second set bit in row j = 2
        with self.assertRaises(VerificationError):
            self.run_check(comps, ac, n)

    def test_hamming_weight_zero_accepted_here(self):
        # the one-hot check alone only proves weight <= 1; weight 0 is caught by the
        # row-sum claim of Shout / Twist (see their tests)
        n, ac = 2, 3
        comps = [comp_tables([1, 2, 3, 4], 3, 1)[0]]
        for u in range(8):
            comps[0][u + 8 * 1] = 0
        self.run_check(comps, ac, n)


class VirtTest(unittest.TestCase):
    def test_virt_d2_d3(self):
        rng = random.Random(5)
        for a, d in ((4, 2), (6, 3)):
            n, T = 3, 8
            addrs = [rng.randrange(1 << a) for _ in range(T)]
            comps = comp_tables(addrs, a, d)
            full = full_table(comps, a, d, T)
            r_k = [random_k(rng) for _ in range(a)]
            c1 = [random_k(rng) for _ in range(n)]
            c2 = [random_k(rng) for _ in range(n)]
            v1 = mle_eval(full, r_k + c1)
            v2 = mle_eval(full, r_k + c2)
            names = [f"w{i}" for i in range(d)]
            g = VirtGroup(names, r_k, [VirtTerm(c1, v1), VirtTerm(c2, v2)])
            proof, claims = virt_prove([g], [comps], a, d, n, tr(), b"v")
            vclaims = virt_verify([g], a, d, n, proof, tr(), b"v")
            self.assertEqual(len(claims), d)
            for c, v in zip(claims, vclaims):
                self.assertEqual(c.value, v.value)
                i = int(c.poly[1:])
                self.assertEqual(mle_eval(comps[i], c.point), c.value)
            bad = VirtGroup(names, r_k, [VirtTerm(c1, v1 + K.ONE), VirtTerm(c2, v2)])
            with self.assertRaises(VerificationError):
                virt_verify([bad], a, d, n, proof, tr(), b"v")


if __name__ == "__main__":
    unittest.main()
