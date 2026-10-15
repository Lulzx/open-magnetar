import hashlib
import unittest

from openmagnetar.hashing import Hasher


class HasherTest(unittest.TestCase):
    def test_profiles(self):
        self.assertEqual(Hasher().digest(b"abc"), hashlib.sha256(b"abc").digest())
        self.assertEqual(Hasher("sha3-256").digest(b"abc"), hashlib.sha3_256(b"abc").digest())
        self.assertEqual(Hasher("sha384").digest_size, 48)
        with self.assertRaises(ValueError):
            Hasher("md5")
