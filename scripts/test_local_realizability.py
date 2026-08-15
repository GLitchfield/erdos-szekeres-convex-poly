#!/usr/bin/env python3
"""Unit tests for the finite sweep-realizability producer and checker."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import sys
import unittest


SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

import check_local_realizability as checker  # noqa: E402
import check_fixed_realization_extensions as extension_checker  # noqa: E402
import check_local_realizability_56 as checker_56  # noqa: E402
import analyze_fixed_realization_extensions as extension_producer  # noqa: E402
import generate_local_realizability as producer  # noqa: E402
import generate_local_realizability_56 as producer_56  # noqa: E402


class LocalRealizabilityTests(unittest.TestCase):
    def test_exact_one_change_words(self) -> None:
        self.assertEqual(checker.exhaustive_fin_four(), (0, 1, 3, 7, 8, 12, 14, 15))

    def test_search_matches_frozen_lean_coordinates(self) -> None:
        found = producer.search_fin_four(checker.exhaustive_fin_four())
        actual = {
            format(mask, "x"): row["points"]
            for mask, row in found.items()
        }
        self.assertEqual(actual, checker.EXPECTED_COORDINATES)

    def test_determinant_conventions_agree(self) -> None:
        for mask_hex, points in checker.EXPECTED_COORDINATES.items():
            producer_result = producer.point_mask(tuple(tuple(point) for point in points))
            self.assertIsNotNone(producer_result)
            mask, _ = producer_result  # type: ignore[misc]
            determinants = [checker.determinant(points, triple)
                            for triple in checker.all_triples(4)]
            checked_mask = sum(int(value > 0) << index
                               for index, value in enumerate(determinants))
            self.assertEqual(mask, int(mask_hex, 16))
            self.assertEqual(checked_mask, mask)

    def test_coordinate_corruption_is_observable(self) -> None:
        points = deepcopy(checker.EXPECTED_COORDINATES["0"])
        original = [checker.determinant(points, triple)
                    for triple in checker.all_triples(4)]
        points[0][1] += 1
        changed = [checker.determinant(points, triple)
                   for triple in checker.all_triples(4)]
        self.assertNotEqual(original, changed)

    def test_decomposition_tree_has_independent_semantics(self) -> None:
        tree = producer_56.decomposition_tree(0, 5)
        self.assertIsNotNone(tree)
        self.assertEqual(checker_56.validate_tree(0, 5, tree), (1 << 5) - 1)

    def test_extension_feasibility_implementations_agree(self) -> None:
        points = tuple(tuple(point) for point in checker.EXPECTED_COORDINATES["0"])
        producer_masks = {
            mask for mask in range(1 << 6)
            if extension_producer.extension_witness(points, mask) is not None
        }
        checker_masks = {
            mask for mask in range(1 << 6)
            if extension_checker.feasible([list(point) for point in points], mask)
        }
        self.assertEqual(producer_masks, checker_masks)


if __name__ == "__main__":
    unittest.main()
