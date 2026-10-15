import random
import unittest

from openmagnetar.field import K, random_k
from openmagnetar.mle import mle_eval
from openmagnetar.ring_switch import (RingSwitchProof, a_eval, a_table, pack,
                                      rs_prove, rs_verify)
from openmagnetar.sumcheck import SumcheckProof, VerificationError
from openmagnetar.transcript import Transcript


def setup(ell=10, seed=11):
    rng = random.Random(seed)
    bits = [rng.getrandbits(1) for _ in range(1 << ell)]
    r = [random_k(rng) for _ in range(ell)]
    return rng, bits, r, mle_eval(bits, r)


class TestRingSwitch(unittest.TestCase):
    def test_pack_matches_convention(self):
        bits = [0] * 256
        bits[1] = 1
        bits[128 + 127] = 1
        P = pack(bits)
        self.assertEqual(P[0], K.X)
        self.assertEqual(P[1], K(1 << 127))

    def test_completeness_and_output_claim(self):
        for ell in (8, 9, 11):
            rng, bits, r, y = setup(ell, ell)
            proof, r_s, v = rs_prove(bits, r, y, Transcript(b"t"))
            self.assertEqual(mle_eval(pack(bits), r_s), v)
            r_s2, v2 = rs_verify(r, y, proof, Transcript(b"t"))
            self.assertEqual((r_s, v), (r_s2, v2))

    def test_a_eval_matches_table(self):
        rng, bits, r, y = setup(10)
        rho = [random_k(rng) for _ in range(7)]
        z = [random_k(rng) for _ in range(3)]
        self.assertEqual(a_eval(r[7:], rho, z), mle_eval(a_table(r[7:], rho), z))

    def test_wrong_value_rejected(self):
        rng, bits, r, y = setup()
        proof, _, _ = rs_prove(bits, r, y, Transcript(b"t"))
        with self.assertRaises(VerificationError):
            rs_verify(r, y + K.ONE, proof, Transcript(b"t"))

    def test_tampered_s_rejected_or_output_wrong(self):
        # Change s_0 and s_1 so that check 1 still holds: the sum-check target then
        # disagrees with P, so either verify raises or the output claim is false.
        from openmagnetar.mle import eq_table
        rng, bits, r, y = setup()
        proof, _, _ = rs_prove(bits, r, y, Transcript(b"t"))
        e = eq_table(r[:7])
        d = random_k(rng)
        s = list(proof.s)
        s[0] = s[0] + d
        s[1] = s[1] + d * e[0] / e[1]
        bad = RingSwitchProof(s, proof.sumcheck)
        P = pack(bits)
        try:
            r_s, v = rs_verify(r, y, bad, Transcript(b"t"))
        except VerificationError:
            return
        self.assertNotEqual(mle_eval(P, r_s), v)

    def test_dishonest_prover_flipped_bit_caught_by_pcs_claim(self):
        # Prover proves for bits' != bits (one flipped bit) against y of bits': the
        # reduction passes, but the output claim concerns P' not P.
        rng, bits, r, _ = setup()
        bits2 = list(bits)
        bits2[5] ^= 1
        y2 = mle_eval(bits2, r)
        proof, r_s, v = rs_prove(bits2, r, y2, Transcript(b"t"))
        self.assertNotEqual(mle_eval(pack(bits), r_s), v)

    def test_tampered_sumcheck_rejected(self):
        rng, bits, r, y = setup()
        proof, r_s, v = rs_prove(bits, r, y, Transcript(b"t"))
        msgs = [list(m) for m in proof.sumcheck.round_msgs]
        msgs[1][0] = msgs[1][0] + K.ONE
        bad = RingSwitchProof(proof.s, SumcheckProof(msgs))
        try:
            r2, v2 = rs_verify(r, y, bad, Transcript(b"t"))
        except VerificationError:
            return
        self.assertNotEqual(mle_eval(pack(bits), r2), v2)

    def test_malformed(self):
        rng, bits, r, y = setup()
        proof, _, _ = rs_prove(bits, r, y, Transcript(b"t"))
        with self.assertRaises(VerificationError):
            rs_verify(r, y, RingSwitchProof(proof.s[:-1], proof.sumcheck), Transcript(b"t"))


if __name__ == "__main__":
    unittest.main()
