#!/usr/bin/env python3
"""Deterministic encoding tests for the k=9 extreme-exchange audit."""

from __future__ import annotations

import hashlib
import sys
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

import check_extreme_exchange_k9 as producer  # noqa: E402
import check_extreme_exchange_k9_model as checker  # noqa: E402


class ExtremeExchangeK9Tests(unittest.TestCase):
    def test_exact_formula_dimensions_and_hashes(self) -> None:
        expected_hashes = {
            "8-9": "f056157ee3af5a3d3827abd86d4f3bad76763564ba1ac068e266771dd1140275",
            "9-8": "4d4a745ddd60e46c9db395b32e7b798187db107971b6b604d6e180bc0386de41",
        }
        for tag, expected_hash in expected_hashes.items():
            clauses, metadata = producer.build_formula(tag)
            self.assertEqual(metadata["variables"], 5440)
            self.assertEqual(len(clauses), 60056)
            self.assertEqual(
                metadata["counts"],
                {"signotope": 19040, "equality_definition": 19040,
                 "no_cap_four": 2380, "no_strong_ten": 19448,
                 "cup_block_units": 140, "forbidden_exchange_cups": 8},
            )
            self.assertEqual(hashlib.sha256(checker.expected_cnf(tag)).hexdigest(),
                             expected_hash)

    def test_equality_auxiliary_truth_table(self) -> None:
        clauses, _ = producer.build_formula("8-9")
        definition = clauses[19040:19044]
        for x in (False, True):
            for y in (False, True):
                for equal in (False, True):
                    assignment = {1: x, 2: y, 681: equal}
                    satisfies = all(any(assignment[abs(lit)] == (lit > 0)
                                        for lit in clause)
                                    for clause in definition)
                    self.assertEqual(satisfies, equal == (x == y))

    def test_contract_does_not_forbid_a_ten_cup(self) -> None:
        for tag in ("8-9", "9-8"):
            clauses, _ = producer.build_formula(tag)
            self.assertFalse(any(len(clause) == 120 and all(literal < 0 for literal in clause)
                                 for clause in clauses))
            self.assertTrue(all(len(clause) == 84 and all(literal < 0 for literal in clause)
                                for clause in clauses[-8:]))


if __name__ == "__main__":
    unittest.main()
