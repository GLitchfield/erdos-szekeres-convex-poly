#!/usr/bin/env python3
"""Regression tests for the exact recurrence used by the Lean additivity nodes."""
from __future__ import annotations

import json
import itertools
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from decomposable_additivity_test import child, contexts
from decomposable_depth2_tables import limits_from_signature
from decomposable_recursive_formula import make_F2


ROOT = Path(__file__).resolve().parents[1]


class LeanContextRecurrenceTest(unittest.TestCase):
    def test_limits_match_literal_sublist_folds(self) -> None:
        # Independent oracle: enumerate precisely Lean's level sublists and greedy
        # endpoint steps, rather than the evaluator's dynamic-programming states.
        def expected(word, maxima, p, q):
            sides = {level: "lower" for level in range(1, len(maxima) + 1)}
            positions = {level: [] for level in sides}
            for x, letter in enumerate(word):
                if letter != "S":
                    level, side = letter
                    sides[level] = side
                    positions[level].append(x)

            def ext(side, top, start, left):
                levels = [level for level in sides
                          if sides[level] == side and (top == 0 or level < top)]
                best = 0
                for size in range(len(levels) + 1):
                    for chosen in itertools.combinations(levels, size):
                        end, count = start, 0
                        for level in chosen:
                            candidates = [x for x in positions[level]
                                          if (x < end if left else end < x)]
                            if candidates:
                                end = max(candidates) if left else min(candidates)
                                count += 1
                        best = max(best, count)
                return best

            limits = []
            for side in ("lower", "upper"):
                chain = ext(side, 0, p, True) + ext(side, 0, q, False)
                join = max([chain] + [
                    ext(side, level, p, True) + ext(side, level, q, False) + maxima[level - 1]
                    for level in sides if sides[level] == side])
                limits.append(max(0, min(3 - chain, 3 - join)))
            return tuple(limits)

        for word, maxima in contexts(2, 2, 2, 4, include_unused_levels=True):
            representatives = [p for p, letter in enumerate(word)
                               if letter == "S" and (p == 0 or word[p - 1] != "S")]
            runs, cups, caps = limits_from_signature(word, maxima, 4, 4, 4, lean=True)
            self.assertEqual(runs, len(representatives))
            for i, p in enumerate(representatives):
                for j in range(i, runs):
                    self.assertEqual((cups[i][j], caps[i][j]),
                                     expected(word, maxima, p, representatives[j]),
                                     (word, maxima, i, j))

    def test_unused_level_contributes_to_join_limit(self) -> None:
        word = ("S", "S")
        maxima = (1,)
        p, cups, caps = limits_from_signature(word, maxima, 3, 3, 3, lean=True)
        self.assertEqual((p, cups[0][0], caps[0][0]), (1, 1, 2))
        self.assertEqual(make_F2(3, 3, 3, include_zero_children=True)(word, maxima), 1)
        self.assertEqual(make_F2(3, 3, 3)(word, maxima), 2)

    def test_generator_includes_missing_and_trailing_levels(self) -> None:
        generated = list(contexts(2, 1, 2, 3, include_unused_levels=True))
        self.assertEqual(len(generated), len(set(generated)))
        self.assertIn((("S", "S"), (1, 1)), generated)
        self.assertIn((("S", (2, "upper"), "S"), (1, 1)), generated)
        self.assertIn((("S", (1, "upper"), "S"), (1, 1)), generated)
        # With two children and at most one external vertex: three empty-external
        # contexts, six at depth one and twelve at depth two.
        self.assertEqual(len(generated), 21)

    def test_literal_limits_use_natural_numbers(self) -> None:
        _, cups, caps = limits_from_signature(("S",), (), 200, 200, 200, lean=True)
        self.assertEqual((cups[0][0], caps[0][0]), (199, 199))
        word = ((3, "lower"), (2, "lower"), (1, "lower"), "S")
        _, cups, _ = limits_from_signature(word, (1, 1, 1), 3, 3, 3, lean=True)
        self.assertEqual(cups[0][0], 0)
        _, historical, _ = limits_from_signature(word, (1, 1, 1), 3, 3, 3)
        self.assertLess(historical[0][0], 0)

    def test_zero_child_contributes_its_positive_sibling(self) -> None:
        word = ("S", (1, "lower"), "S")
        maxima = (1,)
        literal = make_F2(3, 3, 3, include_zero_children=True)
        self.assertEqual(literal(*child(word, maxima, {0}, "lower", 1)), 0)
        self.assertEqual(literal(*child(word, maxima, {2}, "upper", 1)), 1)
        self.assertEqual(literal(word, maxima), 1)
        self.assertEqual(make_F2(3, 3, 3)(word, maxima), 0)

    def test_all_two_child_partitions_include_zero_parents(self) -> None:
        output_root = ROOT / "runs" / "ctx-zero-bound-review"
        output_root.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=output_root) as directory:
            output = Path(directory) / "additivity.json"
            subprocess.run([
                sys.executable, str(ROOT / "scripts" / "decomposable_additivity_test.py"),
                "--case", "3,3,3", "--s-max", "2", "--e-max", "2", "--levels", "2",
                "--recursion", "lean", "--output", str(output),
            ], cwd=ROOT, check=True, capture_output=True, text=True)
            result = json.loads(output.read_text())
        self.assertEqual(result["recursion"], "lean")
        stats = result["stats"]
        self.assertGreater(stats["contexts"], stats["nonzero_contexts"])
        # Each context has exactly two nonempty proper subsets of its two children.
        self.assertEqual(stats["partitions"], 2 * stats["contexts"])
        self.assertEqual(stats["violations"], 0)


if __name__ == "__main__":
    unittest.main()
