#!/usr/bin/env python3
from __future__ import annotations

import itertools
import unittest

import check_decomposable_enumeration as checker
import enumerate_decomposable_colorings as producer


class DecomposableEnumerationTest(unittest.TestCase):
    def test_small_distinct_coloring_counts(self) -> None:
        expected = {1: 1, 2: 1, 3: 2, 4: 8, 5: 62}
        for n, count in expected.items():
            with self.subTest(n=n):
                colorings, _ = producer.enumerate_colorings(n)
                self.assertEqual(len(colorings), count)

    def test_independent_recurrence_matches_producer(self) -> None:
        for n in range(1, 6):
            with self.subTest(n=n):
                colorings, _ = producer.enumerate_colorings(n)
                self.assertEqual(
                    set(colorings), set(checker.replay_colorings(n)))

    def test_explicit_tree_replay_matches_at_four(self) -> None:
        n = 4
        triple_list = tuple(itertools.combinations(range(n), 3))
        all_trees = checker.trees((1 << n) - 1)
        self.assertEqual(len(all_trees), 120)
        replayed = {checker.coloring(tree, triple_list) for tree in all_trees}
        produced, _ = producer.enumerate_colorings(n)
        self.assertEqual(replayed, set(produced))

    def test_every_five_leaf_coloring_is_signotope_and_has_strong_four(self) -> None:
        n = 5
        triple_list = producer.triples(n)
        positions = {triple: index for index, triple in enumerate(triple_list)}
        colorings, _ = producer.enumerate_colorings(n)
        self.assertTrue(all(
            producer.is_signotope(bits, positions, n) for bits in colorings))
        self.assertTrue(all(any(
            producer.is_strong(bits, positions, subset)
            for subset in itertools.combinations(range(n), 4))
            for bits in colorings))


if __name__ == "__main__":
    unittest.main()
