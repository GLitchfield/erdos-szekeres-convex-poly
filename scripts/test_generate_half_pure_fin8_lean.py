from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "generate_half_pure_fin8_lean", ROOT / "scripts/generate_half_pure_fin8_lean.py")
GENERATOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(GENERATOR)


class HalfPureFin8GeneratorTest(unittest.TestCase):
    def test_dense_core_dimensions_and_empty_clause(self) -> None:
        outputs = GENERATOR.generated_outputs(ROOT)
        cnf = outputs[Path("certificates/half-pure-deep-split-fin8-core.cnf")]
        lrat = outputs[Path("certificates/half-pure-deep-split-fin8-core.lrat")]
        variables, clauses = GENERATOR.parse_dimacs(cnf)
        records = GENERATOR.parse_lrat(lrat)
        self.assertEqual(variables, 266)
        self.assertEqual(len(clauses), 483)
        self.assertEqual(len(records), 261)
        self.assertEqual(records[-1][1], ())

    def test_generation_is_byte_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as left, tempfile.TemporaryDirectory() as right:
            left_hashes = GENERATOR.generate(ROOT, Path(left))
            right_hashes = GENERATOR.generate(ROOT, Path(right))
            self.assertEqual(left_hashes, right_hashes)
            self.assertEqual(len(left_hashes), 28)


if __name__ == "__main__":
    unittest.main()
