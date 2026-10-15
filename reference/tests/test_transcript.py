import json
import unittest

from openmagnetar.field import K
from openmagnetar.hashing import Hasher
from openmagnetar.transcript import Transcript, enc, u64le


def script(t):
    t.absorb_bytes(b"test/bytes", b"hello")
    t.absorb_k(b"test/k", K(0x0123456789ABCDEF))
    t.absorb_ks(b"test/ks", [K(1), K.X, K.t(3)])
    return [t.challenge_k(b"test/c1").hex(), t.challenge_k(b"test/c1").hex(),
            [x.hex() for x in t.challenge_ks(b"test/cs", 2)],
            t.challenge_nonzero_k(b"test/nz").hex(),
            t.challenge_index(b"test/idx", 20), t.challenge_index(b"test/idx64", 64)]


class TranscriptTest(unittest.TestCase):
    def test_deterministic_and_sensitive(self):
        a = script(Transcript(b"om/test"))
        self.assertEqual(a, script(Transcript(b"om/test")))
        self.assertNotEqual(a, script(Transcript(b"om/test2")))
        self.assertNotEqual(a, script(Transcript(b"om/test", Hasher("sha3-256"))))
        self.assertNotEqual(a[0], a[1])  # counter

    def test_framing_unambiguous(self):
        t1, t2 = Transcript(b"om/x"), Transcript(b"om/x")
        t1.absorb_bytes(b"a", b"bc")
        t2.absorb_bytes(b"ab", b"c")
        self.assertNotEqual(t1.challenge_k(b"c"), t2.challenge_k(b"c"))

    def test_known_answer_manual(self):
        h = Hasher()
        st = h.digest(b"\x00" + enc(b"openmagnetar/transcript/v1") + enc(b"sha256") + enc(b"om/test"))
        t = Transcript(b"om/test")
        self.assertEqual(t.state, st)
        t.absorb_bytes(b"lbl", b"data")
        st = h.digest(b"\x01" + st + enc(b"lbl") + enc(b"data"))
        self.assertEqual(t.state, st)
        out = h.digest(b"\x02" + st + u64le(0) + enc(b"ch"))
        self.assertEqual(t.challenge_k(b"ch"), K.from_bytes(out[:16]))
        out = h.digest(b"\x02" + st + u64le(1) + enc(b"ch"))
        self.assertEqual(t.challenge_index(b"ch", 10), int.from_bytes(out[:8], "little") & 1023)

    def test_nonzero_retry(self):
        class Z(Hasher):
            n = 0
            def digest(self, data):
                if data[:1] == b"\x02":
                    Z.n += 1
                    if Z.n <= 2:
                        return bytes(32)
                return super().digest(data)
        t = Transcript(b"om/t", Z())
        c = t.challenge_nonzero_k(b"nz")
        self.assertTrue(c)
        self.assertEqual(t.counter, 3)

    def test_index_range(self):
        t = Transcript(b"om/t")
        for bits in (0, 1, 7, 64):
            self.assertTrue(0 <= t.challenge_index(b"i", bits) < (1 << bits))
        with self.assertRaises(ValueError):
            t.challenge_index(b"i", 65)

    def test_sha384(self):
        t = Transcript(b"om/t", Hasher("sha384"))
        self.assertEqual(len(t.state), 48)
        t.challenge_k(b"c")

    def test_kat_file(self):
        import os
        p = os.path.join(os.path.dirname(__file__), "..", "vectors", "02-transcript", "transcript.json")
        if not os.path.exists(p):
            self.skipTest("vectors not generated")
        for v in json.load(open(p))["vectors"]:
            h = Hasher(v["profile"])
            self.assertEqual(script(Transcript(v["protocol_label"].encode(), h)), v["outputs"])
