#!/usr/bin/env python3
"""Unit tests for the local OneChange census producer and checker."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import sys
import unittest


SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

import check_local_constraint_hierarchy as checker  # noqa: E402
import enumerate_local_constraint_hierarchy as producer  # noqa: E402


class LocalConstraintHierarchyTests(unittest.TestCase):
    def test_exact_quadruple_words(self) -> None:
        allowed = [
            pattern for pattern in range(16)
            if producer.one_change(tuple(bool(pattern & (1 << shift))
                                         for shift in range(3, -1, -1)))
        ]
        self.assertEqual(allowed, [0, 1, 3, 7, 8, 12, 14, 15])
        self.assertEqual(
            allowed,
            [pattern for pattern in range(16)
             if checker.at_most_one_change(tuple(bool(pattern & (1 << shift))
                                                 for shift in range(3, -1, -1)))],
        )

    def test_independent_catalogs_agree_through_five(self) -> None:
        generated, _ = producer.enumerate_hierarchy(5)
        self.assertEqual(len(generated[4]), 8)
        self.assertEqual(len(generated[5]), 62)
        self.assertEqual(generated[4], checker.exhaustive_level(4))
        self.assertEqual(generated[5], checker.exhaustive_level(5))

    def test_rightmost_restriction_recovers_edges(self) -> None:
        levels, edges = producer.enumerate_hierarchy(5)
        edge_by_child = {
            child: (parent, pair_mask) for parent, child, pair_mask in edges[5]
        }
        self.assertEqual(len(edge_by_child), len(levels[5]))
        for child in levels[5]:
            self.assertEqual(checker.restrict_rightmost(child, 5), edge_by_child[child])

    def test_declared_symmetries_are_involutions(self) -> None:
        levels, _ = producer.enumerate_hierarchy(5)
        for n in (4, 5):
            states = set(levels[n])
            for state in states:
                reflected = producer.reflect_color(state, n)
                reversed_state = producer.reverse_order(state, n)
                self.assertIn(reflected, states)
                self.assertIn(reversed_state, states)
                self.assertEqual(producer.reflect_color(reflected, n), state)
                self.assertEqual(producer.reverse_order(reversed_state, n), state)

    def test_pair_principal_spectrum_implementations_agree(self) -> None:
        levels, _ = producer.enumerate_hierarchy(5)
        for n in (4, 5):
            for state in levels[n]:
                self.assertEqual(
                    producer.pair_principal_spectrum(state, n),
                    checker.independent_pair_spectrum(state, n),
                )

    def test_document_comparison_rejects_mutation(self) -> None:
        expected, _ = checker.reconstruct(4)
        altered = deepcopy(expected)
        altered["levels"]["4"]["states_hex"][0] = "2"
        with self.assertRaises(checker.VerificationError):
            checker.verify_document(altered, expected)


if __name__ == "__main__":
    unittest.main()
