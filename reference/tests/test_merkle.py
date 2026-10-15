import unittest

from openmagnetar.hashing import Hasher
from openmagnetar.merkle import MerkleTree, hash_leaf, hash_node, verify_multi
from openmagnetar.sumcheck import VerificationError


def leaves(n):
    return [bytes([i]) * (i % 5 + 1) for i in range(n)]


class TestMerkle(unittest.TestCase):
    def setUp(self):
        self.h = Hasher("sha256")

    def test_single_leaf(self):
        t = MerkleTree(self.h, leaves(1))
        self.assertEqual(t.root, hash_leaf(self.h, leaves(1)[0]))
        verify_multi(self.h, t.root, 1, [0], leaves(1), t.open([0]))

    def test_two_leaves_formula(self):
        t = MerkleTree(self.h, leaves(2))
        self.assertEqual(t.root, hash_node(self.h, hash_leaf(self.h, leaves(2)[0]), hash_leaf(self.h, leaves(2)[1])))

    def test_multi_open_all_sizes(self):
        for n in (1, 2, 3, 5, 8, 11, 16):
            L = leaves(n)
            t = MerkleTree(self.h, L)
            for idx in ([0], [n - 1], list(range(0, n, 2)), list(range(n)), [0, n - 1] if n > 1 else [0]):
                idx = sorted(set(idx))
                auth = t.open(idx)
                verify_multi(self.h, t.root, n, idx, [L[i] for i in idx], auth)

    def test_dedup_full_set_needs_no_auth(self):
        t = MerkleTree(self.h, leaves(8))
        self.assertEqual(t.open(list(range(8))), [])

    def test_tamper(self):
        L = leaves(8)
        t = MerkleTree(self.h, L)
        idx = [1, 2, 6]
        auth = t.open(idx)
        good = [L[i] for i in idx]
        bad_leaf = [good[0] + b"x"] + good[1:]
        with self.assertRaises(VerificationError):
            verify_multi(self.h, t.root, 8, idx, bad_leaf, auth)
        for j in range(len(auth)):
            a = list(auth)
            a[j] = bytes([a[j][0] ^ 1]) + a[j][1:]
            with self.assertRaises(VerificationError):
                verify_multi(self.h, t.root, 8, idx, good, a)
        with self.assertRaises(VerificationError):
            verify_multi(self.h, t.root, 8, idx, good, auth[:-1])
        with self.assertRaises(VerificationError):
            verify_multi(self.h, t.root, 8, idx, good, auth + [auth[0]])
        with self.assertRaises(VerificationError):
            verify_multi(self.h, t.root, 8, [2, 1, 6], good, auth)  # not ascending
        with self.assertRaises(VerificationError):
            verify_multi(self.h, t.root, 8, [1, 2, 7], good, auth)  # wrong index

    def test_domain_separation(self):
        # A leaf equal to node preimage must not collide with the node.
        h = self.h
        a, b = hash_leaf(h, b"a"), hash_leaf(h, b"b")
        self.assertNotEqual(hash_leaf(h, a + b), hash_node(h, a, b))

    def test_sha3_profile(self):
        h = Hasher("sha3-256")
        t = MerkleTree(h, leaves(6))
        verify_multi(h, t.root, 6, [3], [leaves(6)[3]], t.open([3]))


if __name__ == "__main__":
    unittest.main()
