import random
import unittest

from openmagnetar.field import K, random_k


class FieldTest(unittest.TestCase):
    def test_axioms(self):
        rng = random.Random(1)
        for _ in range(50):
            a, b, c = (random_k(rng) for _ in range(3))
            self.assertEqual(a * (b + c), a * b + a * c)
            self.assertEqual((a * b) * c, a * (b * c))
            self.assertEqual(a + a, K.ZERO)
            if a:
                self.assertEqual(a * a.inv(), K.ONE)

    def test_modulus(self):
        x127 = K(1 << 127)
        self.assertEqual(x127 * K.X, K(0x87))  # X^128 = X^7+X^2+X+1

    def test_frobenius_on_bits(self):
        for b in (K.ZERO, K.ONE):
            self.assertEqual(b.square(), b)

    def test_encoding(self):
        a = K.X
        self.assertEqual(a.to_bytes(), bytes([2]) + bytes(15))
        self.assertEqual(K.from_hex(a.hex()), a)
        self.assertEqual(K.pack([0, 1, 1]), K(6))

    def test_fermat(self):
        a = random_k(random.Random(2))
        self.assertEqual(a ** (1 << 128), a)


if __name__ == "__main__":
    unittest.main()
