import json
import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

import gen_vectors_07_08 as gen


class VectorsTest(unittest.TestCase):
    def test_vectors_reproduce(self):
        for sect, files in gen.generate().items():
            for name, obj in files.items():
                path = os.path.join(ROOT, "vectors", sect, name)
                with open(path) as f:
                    stored = json.load(f)
                self.assertEqual(json.loads(json.dumps(obj)), stored, f"{sect}/{name}")


if __name__ == "__main__":
    unittest.main()
