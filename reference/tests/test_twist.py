import random
import unittest

from openmagnetar.field import K, random_k
from openmagnetar.mle import mle_eval
from openmagnetar.twist import (FinalMem, TwistClaims, TwistParams, build_witness,
                                honest_claims, lt_eval, lt_table, m0_table, out_table,
                                twist_prove, twist_verify)
from openmagnetar.onehot import bits_of
from openmagnetar.sumcheck import VerificationError
from openmagnetar.transcript import Transcript


def tr():
    return Transcript(b"test/twist")


def setup(a, d, p, n, ell, seed, hot=False):
    rng = random.Random(seed)
    NK, T, L = 1 << a, 1 << n, 1 << ell
    m0 = [rng.getrandbits(L) if rng.random() < 0.5 else 0 for _ in range(NK)]
    if hot:
        m0[0] = 0
    reads = [[rng.randrange(NK) for _ in range(T)] for _ in range(p)]
    writes = [rng.randrange(NK) for _ in range(T)]
    new = [rng.getrandbits(L) for _ in range(T)]
    params = TwistParams("tw", a, d, p, n, ell)
    wit, info = build_witness(params, m0, reads, writes, new)
    r_o = [random_k(rng) for _ in range(ell)]
    r_c = [random_k(rng) for _ in range(n)]
    claims = honest_claims(params, info, r_o, r_c)
    m0t = m0_table(m0, a, ell)
    return params, m0, wit, info, claims, (lambda pt: mle_eval(m0t, pt))


def final_spec(params, info, m, s_out):
    base = s_out << m
    return FinalMem(m, s_out, [info["final"][base + i] for i in range(1 << m)])


class LTTest(unittest.TestCase):
    def test_lt(self):
        n = 4
        for x in range(16):
            for y in range(16):
                v = lt_eval(bits_of(x, n), bits_of(y, n))
                self.assertEqual(v, K(int(x < y)))

    def test_lt_is_mle(self):
        rng = random.Random(1)
        n = 3
        y = [random_k(rng) for _ in range(n)]
        t = lt_table(y)
        x = [random_k(rng) for _ in range(n)]
        # LT~(x, y) multilinear in x: matches the MLE of x -> LT~(x, y) on the cube
        self.assertEqual(lt_eval(x, y), mle_eval(t, x))


class TwistTest(unittest.TestCase):
    def run_case(self, a, d, p, n, ell, seed, final=None, inc_extra=False):
        params, m0, wit, info, claims, m0e = setup(a, d, p, n, ell, seed)
        fin = final_spec(params, info, *final) if final else None
        proof, out = twist_prove(params, m0, wit, claims, tr(), b"T", fin, inc_extra)
        vout = twist_verify(params, m0e, claims, proof, tr(), b"T", fin, inc_extra)
        self.assertEqual([(x.poly, x.point, x.value) for x in out.claims],
                         [(x.poly, x.point, x.value) for x in vout.claims])
        # every output claim is a true evaluation of a committed polynomial
        for x in vout.claims:
            if x.poly.endswith("/inc"):
                self.assertEqual(mle_eval(wit.inc, x.point), x.value)
            else:
                parts = x.poly.split("/")
                kind, i = parts[1], int(parts[2]) - 1
                if kind == "wa":
                    comp = wit.wa[i]
                else:
                    comp = wit.ra[int(kind[2:])][i]
                self.assertEqual(mle_eval(comp, x.point), x.value)
        return params, m0, wit, info, claims, m0e, fin, proof

    def test_reg_like_p2_d1(self):
        self.run_case(3, 1, 2, 3, 6, 11)

    def test_reg_like_p2_d2(self):
        self.run_case(4, 2, 2, 3, 6, 12, final=None, inc_extra=True)

    def test_ram_like_p1_d1(self):
        self.run_case(3, 1, 1, 3, 6, 13, final=(2, 1), inc_extra=True)

    def test_ram_like_p1_d2_final(self):
        self.run_case(4, 2, 1, 3, 6, 14, final=(2, 3), inc_extra=True)

    def test_d3(self):
        self.run_case(6, 3, 1, 2, 4, 15, final=(3, 5))

    def test_real_register_shape(self):
        # K = 64 registers, p = 2, d = 2 (default), L = 64
        self.run_case(6, 2, 2, 3, 6, 16)

    def test_ram_shared_write_address(self):
        # RAM instance: wa components are the ra components (reads == writes)
        rng = random.Random(50)
        a, d, n = 4, 2, 3
        m0 = [rng.getrandbits(64) for _ in range(16)]
        addrs = [rng.randrange(16) for _ in range(8)]
        new = [rng.getrandbits(64) for _ in range(8)]
        params = TwistParams("tw", a, d, 1, n, 6)
        wit, info = build_witness(params, m0, [addrs], addrs, new)
        self.assertEqual(wit.ra[0], wit.wa)
        claims = honest_claims(params, info, [random_k(rng) for _ in range(6)],
                               [random_k(rng) for _ in range(n)])
        self.assertEqual(claims.bits[0], claims.bits[1])
        m0t = m0_table(m0, a, 6)
        proof, _ = twist_prove(params, m0, wit, claims, tr(), b"T")
        twist_verify(params, lambda pt: mle_eval(m0t, pt), claims, proof, tr(), b"T")

    def test_wrong_read_value(self):
        params, m0, wit, info, claims, m0e, fin, proof = self.run_case(4, 2, 2, 3, 6, 21)
        rv = list(claims.rv)
        rv[1] = rv[1] + K.ONE
        bad = TwistClaims(claims.r_o, claims.r_c, rv, claims.wv, claims.bits)
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, bad, proof, tr(), b"T")

    def test_wrong_read_trace(self):
        # prover's read value table differs from the memory: claims built from a
        # corrupted rv, proof built honestly
        params, m0, wit, info, claims, m0e = setup(4, 2, 2, 3, 6, 22)
        info2 = dict(info)
        rv = [list(r) for r in info["rv"]]
        rv[0][3] ^= 1 << 17
        info2["rv"] = rv
        bad = honest_claims(params, info2, claims.r_o, claims.r_c)
        proof, _ = twist_prove(params, m0, wit, bad, tr(), b"T")
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, bad, proof, tr(), b"T")

    def test_wrong_write_value(self):
        params, m0, wit, info, claims, m0e = setup(3, 1, 1, 3, 6, 23)
        bad = TwistClaims(claims.r_o, claims.r_c, claims.rv, claims.wv + K.ONE, claims.bits)
        proof, _ = twist_prove(params, m0, wit, bad, tr(), b"T")
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, bad, proof, tr(), b"T")

    def test_wrong_address_bit(self):
        params, m0, wit, info, claims, m0e = setup(4, 2, 1, 3, 6, 24)
        bits = [list(b) for b in claims.bits]
        bits[0][1] = bits[0][1] + K.ONE
        bad = TwistClaims(claims.r_o, claims.r_c, claims.rv, claims.wv, bits)
        proof, _ = twist_prove(params, m0, wit, bad, tr(), b"T")
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, bad, proof, tr(), b"T")

    def test_hamming_two_read(self):
        params, m0, wit, info, claims, m0e = setup(4, 2, 2, 3, 6, 25)
        wit.ra[1][0][1 + 4 * 2] = 1
        wit.ra[1][0][2 + 4 * 2] = 1
        proof, _ = twist_prove(params, m0, wit, claims, tr(), b"T")
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, claims, proof, tr(), b"T")

    def test_hamming_zero_write(self):
        for d in (1, 2):
            params, m0, wit, info, claims, m0e = setup(4, d, 1, 3, 6, 26)
            ac = 4 // d
            for u in range(1 << ac):
                wit.wa[0][u + (1 << ac) * 4] = 0
            proof, _ = twist_prove(params, m0, wit, claims, tr(), b"T")
            with self.assertRaises(VerificationError):
                twist_verify(params, m0e, claims, proof, tr(), b"T")

    def test_hamming_zero_read(self):
        params, m0, wit, info, claims, m0e = setup(4, 2, 1, 3, 6, 27)
        for u in range(4):
            wit.ra[0][1][u + 4 * 6] = 0
        proof, _ = twist_prove(params, m0, wit, claims, tr(), b"T")
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, claims, proof, tr(), b"T")

    def test_wrong_increment(self):
        # increment table inconsistent with the claimed written value
        params, m0, wit, info, claims, m0e = setup(3, 1, 1, 3, 6, 28)
        wit.inc[5 + 64 * 2] ^= 1
        proof, _ = twist_prove(params, m0, wit, claims, tr(), b"T")
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, claims, proof, tr(), b"T")

    def test_wrong_final_memory(self):
        params, m0, wit, info, claims, m0e, fin, proof = self.run_case(
            4, 2, 1, 3, 6, 29, final=(2, 1))
        words = list(fin.words)
        words[2] ^= 1 << 40
        bad = FinalMem(fin.m, fin.s_out, words)
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, claims, proof, tr(), b"T", bad)

    def test_wrong_final_region(self):
        params, m0, wit, info, claims, m0e, fin, proof = self.run_case(
            4, 1, 1, 3, 6, 30, final=(2, 1))
        other = final_spec(params, info, 2, 2)
        with self.assertRaises(VerificationError):
            twist_verify(params, m0e, claims, proof, tr(), b"T", other)

    def test_final_untouched_region_equals_m0(self):
        # a region never written: final memory equals M0 there
        a, d, p, n, ell = 4, 1, 1, 2, 6
        rng = random.Random(40)
        m0 = [rng.getrandbits(64) for _ in range(16)]
        reads = [[rng.randrange(8) for _ in range(4)]]
        writes = [rng.randrange(8) for _ in range(4)]
        new = [rng.getrandbits(64) for _ in range(4)]
        params = TwistParams("tw", a, d, p, n, ell)
        wit, info = build_witness(params, m0, reads, writes, new)
        claims = honest_claims(params, info, [random_k(rng) for _ in range(6)],
                               [random_k(rng) for _ in range(2)])
        fin = FinalMem(3, 1, m0[8:16])
        m0t = m0_table(m0, a, ell)
        proof, _ = twist_prove(params, m0, wit, claims, tr(), b"T", fin)
        twist_verify(params, lambda pt: mle_eval(m0t, pt), claims, proof, tr(), b"T", fin)


if __name__ == "__main__":
    unittest.main()
