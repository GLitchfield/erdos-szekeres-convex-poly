#!/usr/bin/env python3
from __future__ import annotations

import math
import unittest

from generate_signotope_state_sat import generate, strong_patterns


class SignotopeStateSATTest(unittest.TestCase):
    def test_strong_pattern_count_is_binary_hull_profile_count(self) -> None:
        self.assertEqual(len(strong_patterns(4)), 4)
        self.assertEqual(len(strong_patterns(5)), 8)
        self.assertEqual(len(strong_patterns(6)), 16)

    def test_six_vertex_clause_accounting(self) -> None:
        variables, clauses, origins, counts, pattern_count = generate(6, 4, 6, 6)
        self.assertEqual(len(variables), math.comb(6, 3))
        self.assertEqual(pattern_count, 16)
        self.assertEqual(counts, {
            "signotope": 8 * math.comb(6, 4),
            "no_cap": math.comb(6, 4),
            "no_cup": 1,
            "no_strong": 16,
        })
        self.assertEqual(len(clauses), sum(counts.values()))
        self.assertEqual(len(origins), len(clauses))
        self.assertEqual(sum(kind == "quad" for kind, _, _ in origins), counts["signotope"])
        self.assertEqual(sum(kind == "cap" for kind, _, _ in origins), counts["no_cap"])
        self.assertEqual(sum(kind == "cup" for kind, _, _ in origins), counts["no_cup"])
        self.assertEqual(sum(kind == "strong" for kind, _, _ in origins), counts["no_strong"])

    def test_state566_canonical_clause_accounting(self) -> None:
        variables, clauses, origins, counts, pattern_count = generate(16, 5, 6, 6)
        self.assertEqual(len(variables), 560)
        self.assertEqual(pattern_count, 16)
        self.assertEqual(counts, {
            "signotope": 14_560,
            "no_cap": 4_368,
            "no_cup": 8_008,
            "no_strong": 128_128,
        })
        self.assertEqual(len(clauses), 155_064)
        self.assertEqual(len(origins), len(clauses))


if __name__ == "__main__":
    unittest.main()
