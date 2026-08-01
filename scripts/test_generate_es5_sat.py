from __future__ import annotations

import unittest

from generate_es5_sat import generate


class GenerateES5SATTest(unittest.TestCase):
    def test_encoding_dimensions_and_partition(self) -> None:
        triples, clauses, origins = generate()

        self.assertEqual(len(triples), 84)
        self.assertEqual(len(set(triples)), 84)
        self.assertEqual(len(clauses), 2016)
        self.assertEqual(len(origins), len(clauses))
        self.assertEqual(sum(kind == "quad" for kind, _, _ in origins), 1008)
        self.assertEqual(sum(kind == "five" for kind, _, _ in origins), 1008)

    def test_exactly_eight_strong_five_patterns(self) -> None:
        _, _, origins = generate()
        patterns = {bits for kind, _, bits in origins if kind == "five"}

        self.assertEqual(len(patterns), 8)


if __name__ == "__main__":
    unittest.main()
