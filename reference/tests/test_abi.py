import random
import unittest

from openmagnetar.abi import (AbiError, Params, RAM_BASE, build_m0, decode_region,
                              encode_region, expected_output_mle_eval, extract_output,
                              input_words, memory_map, output_region_bits, program_digest)

P = Params(ram_log_words=12, input_log_words=5, output_log_words=3)


class TestAbi(unittest.TestCase):
    def test_memory_map_alignment(self):
        for A, I, O in [(12, 5, 3), (12, 3, 5), (10, 4, 4), (20, 12, 8)]:
            p = Params(A, I, O)
            m = memory_map(p)
            self.assertEqual(m.input_base % (1 << I), 0)
            self.assertEqual(m.output_base % (1 << O), 0)
            self.assertLessEqual(m.input_base + m.input_words, m.output_base + (1 << max(I, O)) - 0)
            self.assertLessEqual(m.output_base + m.output_words, m.ram_words)
            self.assertGreaterEqual(m.output_base, m.input_base + m.input_words if I >= O else m.input_base)
            self.assertEqual(m.stack_top_addr, RAM_BASE + 8 * m.input_base)
        with self.assertRaises(AbiError):
            Params(6, 6, 3).validate()

    def test_roundtrip(self):
        rng = random.Random(1)
        for n in [0, 1, 7, 8, 9, 100, 8 * 31]:
            d = bytes(rng.randrange(256) for _ in range(n))
            w = encode_region(d, 5)
            self.assertEqual(len(w), 32)
            self.assertEqual(w[0], n)
            self.assertEqual(decode_region(w, 5), d)
        with self.assertRaises(AbiError):
            encode_region(bytes(8 * 31 + 1), 5)

    def test_noncanonical_rejected(self):
        w = encode_region(b"abc", 3)
        w[1] |= 1 << 40
        with self.assertRaises(AbiError):
            decode_region(w, 3)
        w = encode_region(b"abc", 3)
        w[5] = 1
        with self.assertRaises(AbiError):
            decode_region(w, 3)

    def test_input_and_output_via_ram(self):
        mm = memory_map(P)
        m0 = build_m0({3: 7}, b"hello world", P)
        self.assertEqual(m0[3], 7)
        self.assertEqual(m0[mm.input_base], 11)
        self.assertEqual(m0[mm.input_base + 1], int.from_bytes(b"hello wo", "little"))
        self.assertEqual(input_words(b"", P), {})
        ram = {mm.output_base: 3, mm.output_base + 1: int.from_bytes(b"abc", "little")}
        self.assertEqual(extract_output(ram, P), b"abc")
        with self.assertRaises(AbiError):
            build_m0({mm.input_base: 1}, b"", P)

    def test_digest_sensitivity(self):
        c = {0x1000_0000: 0x73}
        base = program_digest(c, 0x1000_0000, {1: 2}, P)
        self.assertNotEqual(base, program_digest({0x1000_0000: 0x13}, 0x1000_0000, {1: 2}, P))
        self.assertNotEqual(base, program_digest(c, 0x1000_0000, {1: 3}, P))
        self.assertEqual(base, program_digest(c, 0x1000_0000, {1: 2, 5: 0}, P))

    def test_digest_hash_profiles(self):
        # 14.3: first 32 bytes of the configured H under every profile.
        import dataclasses
        import hashlib

        from openmagnetar.abi import DIGEST_DOMAIN, Params

        c = {0x1000_0000: 0x93}
        for profile, name in (("sha256", "sha256"), ("sha3-256", "sha3_256"), ("sha384", "sha384")):
            p = dataclasses.replace(P, hash_profile=profile)
            d = program_digest(c, 0x1000_0000, {1: 2}, p)
            self.assertEqual(len(d), 32)
            u64 = lambda x: (x & (2**64 - 1)).to_bytes(8, "little")
            pre = (DIGEST_DOMAIN + bytes([p.ram_log_words, p.input_log_words, p.output_log_words])
                   + u64(p.max_code_words) + u64(0x1000_0000) + u64(1)
                   + u64(0x1000_0000) + (0x93).to_bytes(4, "little")
                   + u64(1) + u64(1) + u64(2))
            self.assertEqual(d, hashlib.new(name, pre).digest()[:32], profile)

    def test_output_mle(self):
        try:
            from openmagnetar.field import K, random_k
            from openmagnetar.mle import mle_eval  # noqa: F401
        except ImportError:
            self.skipTest("mle/field not available")
        rng = random.Random(2)
        out = b"\x01\x02\x03"
        bits = output_region_bits(out, P)
        self.assertEqual(len(bits), 64 * 8)
        # at a Boolean point the MLE equals the table entry
        for idx in [0, 64, 64 + 8, 64 + 9, 200]:
            pt = [K.ONE if (idx >> i) & 1 else K.ZERO for i in range(9)]
            self.assertEqual(expected_output_mle_eval(out, P, pt), K.ONE if bits[idx] else K.ZERO)
        r = [random_k(rng) for _ in range(9)]
        expected_output_mle_eval(out, P, r)


if __name__ == "__main__":
    unittest.main()
