#!/usr/bin/env python3

from __future__ import annotations

import itertools
import tempfile
import unittest
from pathlib import Path

from scripts.generate_mixed567_all_order_lean import (
    Addition,
    LABELS,
    final_text,
    dependency_cone,
    parse_cnf,
    parse_lrat,
    semantic_clause_lemma,
    tree_ranges,
)


class Mixed567CoreGeneratorTests(unittest.TestCase):
    def test_dependency_cone_discards_unused_steps(self) -> None:
        additions = [
            Addition(4, (1,), (1,)),
            Addition(5, (-1,), (2,)),
            Addition(6, (2,), (3,)),
            Addition(7, (), (4, 5)),
        ]
        initial, derived = dependency_cone(3, additions)
        self.assertEqual(initial, {1, 2})
        self.assertEqual(derived, {4, 5, 7})

    def test_parsers_accept_multiline_dimacs_and_deletions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cnf = root / "tiny.cnf"
            proof = root / "tiny.lrat"
            cnf.write_text("p cnf 2 2\n1\n2 0\n-1 -2 0\n", encoding="ascii")
            proof.write_text("3 1 0 1 0\n3 d 1 0\n4 0 2 3 0\n", encoding="ascii")
            variables, clauses = parse_cnf(cnf)
            additions = parse_lrat(proof, len(clauses))
            self.assertEqual(variables, 2)
            self.assertEqual(clauses, [(1, 2), (-1, -2)])
            self.assertEqual([addition.old_id for addition in additions], [3, 4])

    def test_terminal_clause_emitters_type_support_and_discharge_every_subset(self) -> None:
        cases = [
            ("no_cap_five", list(range(5)), 3, 5, "Turn.right"),
            ("no_cup_six", list(range(6)), 3, 6, "Turn.left"),
            ("no_strong_seven", list(range(7)), 4, None, None),
        ]
        for kind, support, subset_size, cardinality, turn in cases:
            subsets = list(itertools.combinations(support, subset_size))
            vocabulary = {
                index: {"kind": "strong" if subset_size == 4 else "triple",
                        "support": list(subset)}
                for index, subset in enumerate(subsets, start=1)
            }
            text = "\n".join(semantic_clause_lemma(
                0, tuple(vocabulary),
                {"kind": kind, "support": [LABELS[value] for value in support]},
                vocabulary,
            ))
            self.assertIn("show Finset (Fin 12) from", text)
            self.assertEqual(text.count("    · exact h"), len(subsets))
            if cardinality is not None:
                self.assertIn(f"(cardinality := {cardinality})", text)
                self.assertIn(turn, text)
            else:
                self.assertIn("isStrongPolygonSet_image_of_strongAtoms", text)

    def test_final_theorem_contract_and_balanced_ranges_are_deterministic(self) -> None:
        ranges = tree_ranges(14773, 4)
        self.assertEqual(len(ranges), 16)
        self.assertEqual(ranges[0][0], 0)
        self.assertEqual(ranges[-1][1], 14773)
        self.assertTrue(all(left[1] == right[0]
                            for left, right in zip(ranges, ranges[1:])))
        generated = final_text([], ranges, {})
        self.assertIn("theorem mixed567AllOrderFiniteTheorem : Mixed567FiniteTheorem", generated)
        self.assertIn("theorem mixedCarrierOnlyOmissionNormalForm_forces_target567", generated)
        for premise in ("hsystem", "hfirstCard", "hsecondCard",
                        "hcarrierDisjoint", "hOne", "hnormal"):
            self.assertIn(premise, generated)


if __name__ == "__main__":
    unittest.main()
