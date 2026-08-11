#!/usr/bin/env python3
"""Unit tests for the deterministic k=9 Lean generator and independent audit."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


generator = load_module("generate_diagonal_k9_lean", SCRIPT_DIR / "generate_diagonal_k9_lean.py")
checker = load_module("check_diagonal_k9_semantics", SCRIPT_DIR / "check_diagonal_k9_semantics.py")


class DiagonalK9GeneratorTests(unittest.TestCase):
    def test_strong_patterns_are_exactly_middle_determined(self) -> None:
        self.assertEqual(len(generator.STRONG_PATTERNS), 128)
        local = generator.triples(range(9))
        for pattern in generator.STRONG_PATTERNS:
            by_middle: dict[int, bool] = {}
            for (_, middle, _), value in zip(local, pattern):
                self.assertIn(middle, range(1, 8))
                if middle in by_middle:
                    self.assertEqual(by_middle[middle], value)
                by_middle[middle] = value
            self.assertEqual(set(by_middle), set(range(1, 8)))

    def test_independent_pattern_enumeration_agrees(self) -> None:
        self.assertEqual(set(generator.STRONG_PATTERNS), set(checker.STRONG_PATTERNS))

    def test_source_clause_counts(self) -> None:
        expected = {"quad": 10920, "cap": 1365, "cup": 5005, "strong": 640640, "unit": 91}
        for orientation in generator.ORIENTATIONS:
            counts = {family: 0 for family in expected}
            for _, origin in generator.source_clauses(orientation):
                counts[origin.kind] += 1
            self.assertEqual(counts, expected)
            self.assertEqual(sum(counts.values()), 658021)

    def test_balanced_chunking_preserves_order(self) -> None:
        items = list(map(str, range(1157)))
        chunks = generator.balanced_chunks(items, 16)
        self.assertEqual([item for chunk in chunks for item in chunk], items)
        self.assertLessEqual(max(map(len, chunks)) - min(map(len, chunks)), 1)

    def test_frozen_dense_maps_reconstruct(self) -> None:
        repo = SCRIPT_DIR.parent
        run_dir = repo / "runs/agents/20260810-three-route-forward/state567"
        for orientation in generator.ORIENTATIONS:
            old_variables, clauses, origins = generator.retained_clauses(run_dir, orientation)
            self.assertEqual(len(old_variables), orientation.expected_variables)
            self.assertEqual(len(clauses), orientation.expected_clauses)
            counts = {
                family: sum(origin.kind == family for origin in origins)
                for family in orientation.expected_families
            }
            self.assertEqual(counts, orientation.expected_families)


if __name__ == "__main__":
    unittest.main()
