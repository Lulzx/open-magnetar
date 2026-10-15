import math
import unittest

from openmagnetar import ligerito as lg
from openmagnetar import params as P

LOG_TS = (16, 20, 22, 24)


class TestLedger(unittest.TestCase):
    def test_provable_120_every_round(self):
        for lt in LOG_TS:
            L = P.ledger(lt)
            self.assertTrue(L.provable)
            for r in L.rows:
                self.assertGreaterEqual(r.rbr_bits, 120 - 1e-9, (lt, r.step, r.rbr_bits))

    def test_totals_close_to_120(self):
        # the per-reduction totals stay above 119.9 bits; the union over all rows is reported, not claimed as 120
        for lt in LOG_TS:
            L = P.ledger(lt)
            self.assertGreater(min(r.tot_bits for r in L.rows), 119.9)
            self.assertGreater(L.total_error_bits, 114)

    def test_conservative_bound_without_reps_fails(self):
        # documents the gap of 04 4.7 (before the fix): gap term is below 120 bits without amplification
        for lt in (20, 22, 24):
            m = P.Machine(lt)
            n = m.n_pack
            ks = tuple(lg.schedule(n))
            p = lg.LigeritoParams(n, ks, (2,) * len(ks), (177,) * len(ks))
            L = P.ledger(lt, params=p)
            gaps = [r.rbr_bits for r in L.rows if "proximity gap" in r.step]
            self.assertLess(min(gaps), 120)
            self.assertLess(L.min_rbr_bits, 120)

    def test_default_params_use_amplification(self):
        for lt in LOG_TS:
            p = P.ledger(lt).params
            self.assertTrue(p.gs and all(g >= 2 for g in p.gs))
            for i, row in enumerate(r for r in P.ledger(lt).rows if "proximity gap" in r.step):
                self.assertGreaterEqual(row.bits_direct, 120)

    def test_conjectured_flagged(self):
        for lt in LOG_TS:
            L = P.ledger(lt, "conjectured-100")
            self.assertFalse(L.provable)
            self.assertLess(L.min_rbr_bits, 120)
            self.assertTrue(any(not r.provable for r in L.rows))

    def test_formulas_match_sections(self):
        m = P.Machine(22)
        L = P.ledger(22)
        row = {r.step: r for r in L.rows}
        self.assertEqual(row["Spartan inner sum-check (single, both relations)"].tot_num, 28)
        self.assertEqual(row["Router shift"].tot_num, 4 * (22 + 15))
        self.assertEqual(row["Router store"].tot_num, 6 * (22 + 9))
        self.assertEqual(row["Ring switching"].tot_num, 7 + 2 * m.n_pack)
        # 06 Lemma 6.2: eps_vsp = (8(rho+s) + 1 + 2 nu)/|K|
        sp = sum(r.tot_num for k, r in row.items() if k.startswith("Spartan"))
        self.assertEqual(sp, 8 * (10 + 20) + 1 + 28)

    def test_mosaic_claim_cap(self):
        # the powers-of-gamma batching of 03 3.6 / 05 5.7 needs <= 256 claims for 120 bits
        ok = P.ledger(22, machine=P.Machine(22, mosaic_claims=256))
        bad = P.ledger(22, machine=P.Machine(22, mosaic_claims=300))
        self.assertGreaterEqual(ok.min_rbr_bits, 120 - 1e-9)
        self.assertLess(bad.min_rbr_bits, 120)

    def test_sizes_monotone(self):
        a = P.proof_size_bytes(lg.make_params(20))
        b = P.proof_size_bytes(lg.make_params(24))
        self.assertLess(a, b)
        self.assertLess(P.proof_size_bytes(lg.make_params(24, "conjectured-100")), b)

    def test_reference_prover_rejects_reps(self):
        p = lg.make_params(14)
        self.assertTrue(p.gs)
        with self.assertRaises(NotImplementedError):
            lg.open_(p, None, None, [], None, None)

    def test_small_n_unchanged_encoding(self):
        p = lg.LigeritoParams(10, (3, 3), (1, 2), (6, 5))
        self.assertEqual(len(p.encode()), 8 * (2 + 3 * 2))


if __name__ == "__main__":
    unittest.main()
