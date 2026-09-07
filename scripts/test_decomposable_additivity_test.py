#!/usr/bin/env python3
"""Regression tests for the exact recurrence used by the Lean additivity nodes."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from decomposable_additivity_test import child
from decomposable_recursive_formula import make_F2


ROOT = Path(__file__).resolve().parents[1]


class LeanContextRecurrenceTest(unittest.TestCase):
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
