import os
import random
import unittest

from openmagnetar.field import K, random_k
from openmagnetar.mle import eq_table, mle_eval
from openmagnetar.router import (KIND_NAMES, RouterProof, apply_shift, apply_store,
                                 shift_R_eval, shift_entries, shift_prove, shift_source,
                                 shift_valid, shift_verify, shift_witness, store_entries,
                                 store_R_eval, store_prove, store_valid, store_verify,
                                 store_witness)
from openmagnetar.sumcheck import VerificationError
from openmagnetar.transcript import Transcript


def tr():
    return Transcript(b"test/router")


class ShiftSpecTest(unittest.TestCase):
    def test_entries_match_semantics_64(self):
        rng = random.Random(1)
        W = 64
        ent = shift_entries(6)
        by_h = {}
        for o, u, h in ent:
            by_h.setdefault(h, []).append((o, u))
        # each output has at most one source
        for h, lst in by_h.items():
            os_ = [o for o, _ in lst]
            self.assertEqual(len(os_), len(set(os_)))
        self.assertEqual(len(ent), 12512)
        for kind in range(8):
            for amt in range(64):
                h = amt + 64 * kind
                if not shift_valid(kind, amt):
                    self.assertNotIn(h, by_h)
                    continue
                for _ in range(3):
                    src = rng.getrandbits(64)
                    y = 0
                    for o, u in by_h.get(h, []):
                        y |= ((src >> u) & 1) << o
                    self.assertEqual(y, apply_shift(kind, amt, src), (KIND_NAMES[kind], amt))

    def test_known_values(self):
        self.assertEqual(apply_shift(2, 4, 0x8000000000000000), 0xF800000000000000)
        self.assertEqual(apply_shift(3, 1, 0x40000000), 0xFFFFFFFF80000000)
        self.assertEqual(apply_shift(4, 0, 0x80000000), 0xFFFFFFFF80000000)
        self.assertEqual(apply_shift(4, 1, 0x80000000), 0x40000000)
        self.assertEqual(apply_shift(5, 4, 0x80000000), 0xFFFFFFFFF8000000)
        self.assertEqual(apply_shift(6, 0, 0x1_8000_0000), 0xFFFFFFFF80000000)
        self.assertEqual(apply_shift(7, 0, 0x1_8000_0000), 0x80000000)
        self.assertEqual(apply_shift(3, 32, 5), 0)
        self.assertEqual(apply_shift(6, 3, 5), 0)

    def test_R_eval_matches_mle(self):
        rng = random.Random(2)
        wb = 3
        ent = shift_entries(wb)
        W = 1 << wb
        table = [0] * (W * W * 8 * W)       # o + W*(u + W*h)
        for o, u, h in ent:
            table[o + W * (u + W * h)] = 1
        pt = [random_k(rng) for _ in range(wb + wb + wb + 3)]
        self.assertEqual(shift_R_eval(pt[:wb], pt[wb:2 * wb], pt[2 * wb:], wb),
                         mle_eval(table, pt))


class StoreSpecTest(unittest.TestCase):
    def test_entries_match_semantics_64(self):
        rng = random.Random(3)
        ent = store_entries(6)
        self.assertEqual(len(ent), 512)
        for h in range(4):
            for a in range(8):
                for _ in range(3):
                    old, src = rng.getrandbits(64), rng.getrandbits(64)
                    y = 0
                    for o, u, hh, aa in ent:
                        if hh == h and aa == a:
                            bit = ((old >> u) & 1) if u < 64 else ((src >> (u - 64)) & 1)
                            y ^= bit << o
                    self.assertEqual(y, apply_store(old, src, h, a))
                    if not store_valid(h, a):
                        self.assertEqual(y, 0)
        # concrete cases
        self.assertEqual(apply_store(0, 0xAABBCCDD, 0, 3), 0xDD << 24)
        self.assertEqual(apply_store(0xFF << 24, 0xDD, 0, 3), (0xFF ^ 0xDD) << 24)
        self.assertEqual(apply_store(0, 0x1122334455667788, 2, 4), 0x55667788 << 32)

    def test_R_eval_matches_mle(self):
        rng = random.Random(4)
        wb = 4
        ent = store_entries(wb)
        W = 1 << wb
        # index o + W*(u + 2W*(h + 4*a))
        table = [0] * (W * 2 * W * 4 * 2)
        for o, u, h, a in ent:
            table[o + W * (u + 2 * W * (h + 4 * a))] = 1
        pt = [random_k(rng) for _ in range(wb + wb + 1 + 2 + 1)]
        self.assertEqual(store_R_eval(pt[:wb], pt[wb:2 * wb + 1], pt[2 * wb + 1:2 * wb + 3],
                                      pt[2 * wb + 3:], wb), mle_eval(table, pt))


def shift_case(n, wb, seed, routes=None):
    rng = random.Random(seed)
    W, T = 1 << wb, 1 << n
    cycles = []
    for j in range(T):
        src = rng.getrandbits(W)
        if rng.random() < 0.25:
            cycles.append((src, None))
        else:
            while True:
                kind = rng.randrange(8)
                amt = rng.randrange(W)
                if shift_valid(kind, amt, wb):
                    break
            cycles.append((src, (amt, kind)))
    wit = shift_witness(cycles, wb)
    r_o = [random_k(rng) for _ in range(wb)]
    r_j = [random_k(rng) for _ in range(n)]
    y = mle_eval(wit["Y"], r_o + r_j)
    return wit, r_o, r_j, y


class ShiftProtocolTest(unittest.TestCase):
    def check(self, n, wb, seed):
        wit, r_o, r_j, y = shift_case(n, wb, seed)
        proof, claims = shift_prove(n, wit, r_o, r_j, y, tr(), b"sh", wb)
        vc = shift_verify(n, r_o, r_j, y, proof, tr(), b"sh", wb)
        self.assertEqual([(c.poly, c.point, c.value) for c in claims],
                         [(c.poly, c.point, c.value) for c in vc])
        tabs = {"shift/src": wit["X"], "shift/qlo": wit["Qlo"], "shift/qhi": wit["Qhi"]}
        for c in vc:
            self.assertEqual(mle_eval(tabs[c.poly], c.point), c.value)
        return wit, r_o, r_j, y, proof

    def test_wb3(self):
        self.check(2, 3, 1)

    def test_wb3_n3(self):
        self.check(3, 3, 2)

    def test_wrong_output_claim(self):
        wit, r_o, r_j, y, proof = self.check(2, 3, 3)
        with self.assertRaises(VerificationError):
            shift_verify(2, r_o, r_j, y + K.ONE, proof, tr(), b"sh", 3)

    def test_wrong_shift_output(self):
        # prover's Y has a flipped bit; claim built from that Y
        wit, r_o, r_j, y = shift_case(2, 3, 4)
        Y = list(wit["Y"])
        Y[5] ^= 1
        y2 = mle_eval(Y, r_o + r_j)
        proof, _ = shift_prove(2, wit, r_o, r_j, y2, tr(), b"sh", 3)
        with self.assertRaises(VerificationError):
            shift_verify(2, r_o, r_j, y2, proof, tr(), b"sh", 3)

    def test_nonshift_cycle_output_must_be_zero(self):
        wit = shift_witness([(0x5A, None), (0x5A, None), (0x33, (1, 0)), (1, None)], 3)
        rng = random.Random(9)
        r_o = [random_k(rng) for _ in range(3)]
        r_j = [random_k(rng) for _ in range(2)]
        Y = list(wit["Y"])
        Y[0 + 8 * 1] = 1          # nonzero output on a cycle with zero selector
        y2 = mle_eval(Y, r_o + r_j)
        proof, _ = shift_prove(2, wit, r_o, r_j, y2, tr(), b"sh", 3)
        with self.assertRaises(VerificationError):
            shift_verify(2, r_o, r_j, y2, proof, tr(), b"sh", 3)

    def test_wb6(self):
        self.check(1, 6, 5)


def store_case(n, wb, seed, nonstore=0.25):
    rng = random.Random(seed)
    W, T = 1 << wb, 1 << n
    nbytes = W // 8
    cycles = []
    for j in range(T):
        old, src = rng.getrandbits(W), rng.getrandbits(W)
        if rng.random() < nonstore:
            cycles.append((old, src, None))
        else:
            while True:
                h, a = rng.randrange(4), rng.randrange(nbytes)
                if store_valid(h, a, wb):
                    break
            cycles.append((old, src, (h, a)))
    wit = store_witness(cycles, wb)
    r_o = [random_k(rng) for _ in range(wb)]
    r_j = [random_k(rng) for _ in range(n)]
    y = mle_eval(wit["Inc"], r_o + r_j)
    return wit, r_o, r_j, y


class StoreProtocolTest(unittest.TestCase):
    def check(self, n, wb, seed):
        wit, r_o, r_j, y = store_case(n, wb, seed)
        proof, claims = store_prove(n, wit, r_o, r_j, y, tr(), b"st", wb)
        vc = store_verify(n, r_o, r_j, y, proof, tr(), b"st", wb)
        self.assertEqual([(c.poly, c.point, c.value) for c in claims],
                         [(c.poly, c.point, c.value) for c in vc])
        for c in vc:
            if c.poly == "store/src":
                t = wit["X"]
            elif c.poly == "store/q":
                t = wit["Q"]
            else:
                t = wit["abits"][int(c.poly[-1])]
            self.assertEqual(mle_eval(t, c.point), c.value)
        return wit, r_o, r_j, y, proof

    def test_wb4(self):
        self.check(2, 4, 1)

    def test_wb5(self):
        self.check(2, 5, 2)

    def test_wb6(self):
        self.check(1, 6, 3)

    def test_wb6_n2(self):
        self.check(2, 6, 4)

    def test_wrong_increment_claim(self):
        wit, r_o, r_j, y, proof = self.check(2, 4, 5)
        with self.assertRaises(VerificationError):
            store_verify(2, r_o, r_j, y + K.ONE, proof, tr(), b"st", 4)

    def test_wrong_store_increment(self):
        wit, r_o, r_j, y = store_case(2, 4, 6)
        Inc = list(wit["Inc"])
        Inc[3] ^= 1
        y2 = mle_eval(Inc, r_o + r_j)
        proof, _ = store_prove(2, wit, r_o, r_j, y2, tr(), b"st", 4)
        with self.assertRaises(VerificationError):
            store_verify(2, r_o, r_j, y2, proof, tr(), b"st", 4)

    def test_nonstore_cycle_inc_must_be_zero(self):
        wit = store_witness([(0xABCD, 0x1234, None), (0xABCD, 0x1234, (0, 1)),
                             (7, 9, None), (0, 0, None)], 4)
        rng = random.Random(10)
        r_o = [random_k(rng) for _ in range(4)]
        r_j = [random_k(rng) for _ in range(2)]
        Inc = list(wit["Inc"])
        Inc[2 + 16 * 0] = 1       # increment on a cycle with an all-zero selector
        y2 = mle_eval(Inc, r_o + r_j)
        proof, _ = store_prove(2, wit, r_o, r_j, y2, tr(), b"st", 4)
        with self.assertRaises(VerificationError):
            store_verify(2, r_o, r_j, y2, proof, tr(), b"st", 4)

    def test_wrong_offset_witness(self):
        # offset bits committed differently from the ones the increment used
        wit, r_o, r_j, y = store_case(2, 4, 7, nonstore=0.0)
        wit["abits"][0] = [1 - b for b in wit["abits"][0]]
        proof, _ = store_prove(2, wit, r_o, r_j, y, tr(), b"st", 4)
        with self.assertRaises(VerificationError):
            store_verify(2, r_o, r_j, y, proof, tr(), b"st", 4)


if __name__ == "__main__":
    unittest.main()
