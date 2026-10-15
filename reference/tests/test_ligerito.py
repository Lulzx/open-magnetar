import dataclasses
import random
import unittest

from openmagnetar import ligerito as lg
from openmagnetar.field import K, random_k
from openmagnetar.mle import mle_eval
from openmagnetar.pcs import BitPCS, LigeritoPCS
from openmagnetar.sumcheck import VerificationError
from openmagnetar.transcript import Transcript


def run(p, seed=1):
    rng = random.Random(seed)
    pcs = LigeritoPCS(p)
    tab = [random_k(rng) for _ in range(1 << p.n)]
    tr = Transcript(b"t")
    cm, st = pcs.commit(tab, tr)
    r = [random_k(rng) for _ in range(p.n)]
    y, pf = pcs.open(st, r, tr)
    return pcs, tab, cm, r, y, pf


def check(pcs, cm, r, y, pf):
    tv = Transcript(b"t")
    pcs.absorb_commitment(cm, tv)
    pcs.verify(cm, r, y, pf, tv)


class TestLigerito(unittest.TestCase):
    P = lg.LigeritoParams(10, (3, 3), (1, 2), (6, 5))

    def test_completeness(self):
        for p in (lg.LigeritoParams(8, (3,), (1,), (5,)), self.P,
                  lg.LigeritoParams(9, (2, 2, 2), (2, 1, 2), (4, 4, 4))):
            pcs, tab, cm, r, y, pf = run(p)
            self.assertEqual(y, mle_eval(tab, r))
            check(pcs, cm, r, y, pf)

    def test_wrong_value(self):
        pcs, tab, cm, r, y, pf = run(self.P)
        with self.assertRaises(VerificationError):
            check(pcs, cm, r, y + K.ONE, pf)

    def test_wrong_point(self):
        pcs, tab, cm, r, y, pf = run(self.P)
        r2 = list(r)
        r2[0] = r2[0] + K.ONE
        with self.assertRaises(VerificationError):
            check(pcs, cm, r2, y, pf)

    def test_tamper_everything(self):
        pcs, tab, cm, r, y, pf = run(self.P)
        flip = lambda x: x + K.ONE
        cases = []
        # sumcheck message
        c = dataclasses.replace(pf)
        c.sumchecks = [dataclasses.replace(s, round_msgs=[list(m) for m in s.round_msgs]) for s in pf.sumchecks]
        c.sumchecks[0].round_msgs[0][0] = flip(c.sumchecks[0].round_msgs[0][0])
        cases.append(c)
        # opened column value
        c = dataclasses.replace(pf)
        c.openings = [dataclasses.replace(o, columns=[list(col) for col in o.columns]) for o in pf.openings]
        c.openings[0].columns[0][0] = flip(c.openings[0].columns[0][0])
        cases.append(c)
        # Merkle auth path
        c = dataclasses.replace(pf)
        c.openings = [dataclasses.replace(o, auth=list(o.auth)) for o in pf.openings]
        c.openings[1].auth[0] = bytes([c.openings[1].auth[0][0] ^ 1]) + c.openings[1].auth[0][1:]
        cases.append(c)
        # next-level root
        c = dataclasses.replace(pf)
        c.roots = [bytes([pf.roots[0][0] ^ 1]) + pf.roots[0][1:]]
        cases.append(c)
        # final polynomial
        c = dataclasses.replace(pf)
        c.final = list(pf.final)
        c.final[0] = flip(c.final[0])
        cases.append(c)
        for c in cases:
            with self.assertRaises(VerificationError):
                check(pcs, cm, r, y, c)

    def test_wrong_commitment(self):
        pcs, tab, cm, r, y, pf = run(self.P)
        cm2 = dataclasses.replace(cm, root=bytes(32))
        with self.assertRaises(VerificationError):
            check(pcs, cm2, r, y, pf)

    def test_cheating_prover_inconsistent_fold(self):
        # A prover that commits to a level-1 polynomial that is not the fold must fail
        # (with enough queries it is caught with overwhelming probability here).
        p = lg.LigeritoParams(10, (3, 3), (1, 2), (40, 5))
        rng = random.Random(5)
        pcs = LigeritoPCS(p)
        tab = [random_k(rng) for _ in range(1 << p.n)]
        tr = Transcript(b"t")
        cm, st = pcs.commit(tab, tr)
        r = [random_k(rng) for _ in range(p.n)]
        orig = lg.commit_level

        def evil(h, f, k, rr):
            if len(f) == 1 << (p.n - p.ks[0]):
                f = list(f)
                f[3] = f[3] + K.ONE
            return orig(h, f, k, rr)

        lg.commit_level = evil
        try:
            y, pf = pcs.open(st, r, tr)
        finally:
            lg.commit_level = orig
        with self.assertRaises(VerificationError):
            check(pcs, cm, r, y, pf)

    def test_params_and_queries(self):
        self.assertEqual(lg.queries_provable(2, 120), 177)
        self.assertEqual(lg.queries_provable(1, 120), 290)
        self.assertEqual(lg.queries_conjectured(2, 100), 50)
        self.assertEqual(lg.schedule(24), [5, 5, 4, 4])
        self.assertEqual(lg.schedule(20), [5, 5, 4])
        self.assertEqual(lg.schedule(22), [4, 4, 4, 4])
        for d in lg.soundness_bits(lg.make_params(24)):
            self.assertGreaterEqual(d["query"], 120)
            self.assertGreaterEqual(d["sumcheck"], 120)
            self.assertGreaterEqual(d["batch"], 120)

    def test_bitpcs_end_to_end_and_negative(self):
        ell = 11  # packed n = 4 variables
        p = lg.LigeritoParams(ell - 7, (2,), (1,), (6,))
        rng = random.Random(3)
        bits = [rng.getrandbits(1) for _ in range(1 << ell)]
        b = BitPCS(p)
        tr = Transcript(b"t")
        cm, st = b.commit(bits, tr)
        r = [random_k(rng) for _ in range(ell)]
        y, pf = b.open(st, r, tr)
        self.assertEqual(y, mle_eval(bits, r))
        tv = Transcript(b"t")
        b.pcs.absorb_commitment(cm, tv)
        b.verify(cm, r, y, pf, tv)
        tv = Transcript(b"t")
        b.pcs.absorb_commitment(cm, tv)
        with self.assertRaises(VerificationError):
            b.verify(cm, r, y + K.ONE, pf, tv)
        # a prover opening a different bit vector against this commitment
        bits2 = list(bits)
        bits2[9] ^= 1
        tr = Transcript(b"t")
        cm2, st2 = b.commit(bits2, tr)
        tr = Transcript(b"t")
        b.pcs.absorb_commitment(cm, tr)
        st_bad = (st[0], bits2)  # claims bits2 but commitment/state is of bits
        y2 = mle_eval(bits2, r)
        from openmagnetar import ring_switch as rsw
        rs_proof, r_s, v = rsw.rs_prove(bits2, r, y2, tr)
        from openmagnetar.mle import mle_eval as me
        yp = me(st[0].f, r_s)
        pf2 = lg.open_(p, b.pcs.h, st[0], r_s, yp, tr)
        tv = Transcript(b"t")
        b.pcs.absorb_commitment(cm, tv)
        with self.assertRaises(VerificationError):
            b.verify(cm, r, y2, (rs_proof, pf2), tv)


if __name__ == "__main__":
    unittest.main()
