import random
import unittest

from openmagnetar.field import K, random_k
from openmagnetar.mle import bind_low, eq_eval, eq_table, mle_eval


def brute(table, r):
    acc = K.ZERO
    for i, v in enumerate(table):
        bits = [K((i >> j) & 1) for j in range(len(r))]
        acc = acc + K._coerce(v) * eq_eval(r, bits)
    return acc


class MleTest(unittest.TestCase):
    def test_eq_table(self):
        rng = random.Random(3)
        r = [random_k(rng) for _ in range(4)]
        t = eq_table(r)
        self.assertEqual(len(t), 16)
        for i in range(16):
            self.assertEqual(t[i], eq_eval(r, [K((i >> j) & 1) for j in range(4)]))
        self.assertEqual(sum((x for x in t), K.ZERO), K.ONE)

    def test_mle_eval_bruteforce(self):
        rng = random.Random(4)
        for n in range(0, 6):
            r = [random_k(rng) for _ in range(n)]
            tk = [random_k(rng) for _ in range(1 << n)]
            tb = [rng.getrandbits(1) for _ in range(1 << n)]
            self.assertEqual(mle_eval(tk, r), brute(tk, r))
            self.assertEqual(mle_eval(tb, r), brute(tb, r))

    def test_boolean_point_and_low_order(self):
        t = [K(i + 1) for i in range(8)]
        # index 5 = bits (1,0,1), x_1 is LSB
        self.assertEqual(mle_eval(t, [K.ONE, K.ZERO, K.ONE]), t[5])
        r = [K(7), K(9), K(11)]
        self.assertEqual(mle_eval(t, r), mle_eval(bind_low(t, r[0]), r[1:]))

    def test_packing_identity(self):
        # ring-switching identities of spec 01
        rng = random.Random(5)
        l = 9
        w = [rng.getrandbits(1) for _ in range(1 << l)]
        P = [K.pack(w[128 * v:128 * v + 128]) for v in range(1 << (l - 7))]
        r = [random_k(rng) for _ in range(l)]
        rlo, rhi = r[:7], r[7:]
        s = [mle_eval([w[j + 128 * v] for v in range(1 << (l - 7))], rhi) for j in range(128)]
        e = eq_table(rlo)
        self.assertEqual(mle_eval(w, r), sum((e[j] * s[j] for j in range(128)), K.ZERO))
        self.assertEqual(mle_eval(P, rhi), sum((K(1 << j) * s[j] for j in range(128)), K.ZERO))
