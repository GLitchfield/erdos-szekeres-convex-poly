import importlib.util
import itertools
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "generate_predecessor_half_fin13_sat",
    ROOT / "scripts/generate_predecessor_half_fin13_sat.py",
)
GENERATOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(GENERATOR)


class PredecessorHalfFin13SATTest(unittest.TestCase):
    def test_strong_pattern_counts(self) -> None:
        self.assertEqual(len(GENERATOR.strong_patterns(5)[1]), 8)
        self.assertEqual(len(GENERATOR.strong_patterns(6)[1]), 16)

    def test_frozen_formula_counts(self) -> None:
        variables, clauses, counts = GENERATOR.generate(13)
        self.assertEqual(counts["triple_variables"], 286)
        self.assertEqual(counts["selector_variables"], 10296)
        self.assertEqual(counts["one_change"], 8 * len(list(itertools.combinations(range(13), 4))))
        self.assertEqual(counts["no_strong_six"], 16 * 1716)
        self.assertEqual(counts["strong_five_selector_implications"], 102960)
        self.assertEqual(counts["every_seven_has_strong_five"], 1716)
        self.assertEqual(variables, 10582)
        self.assertEqual(len(clauses), 137852)

    def test_other_size_rejected(self) -> None:
        with self.assertRaises(ValueError):
            GENERATOR.generate(12)


if __name__ == "__main__":
    unittest.main()
