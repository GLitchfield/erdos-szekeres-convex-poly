from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "generate_half_pure_singleton_fin10_lean",
    ROOT / "scripts/generate_half_pure_singleton_fin10_lean.py",
)
GENERATOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(GENERATOR)


class HalfPureSingletonFin10GeneratorTest(unittest.TestCase):
    def test_exact_reconstruction_and_core_dimensions(self) -> None:
        source = ROOT / GENERATOR.SOURCE_REL
        core = GENERATOR.dense_core(
            GENERATOR.read_frozen(source, "formula.cnf"),
            GENERATOR.read_frozen(source, "primary.lrat"),
        )
        variables, clauses = GENERATOR.parse_dimacs(core["core_cnf"])
        additions, deletions = GENERATOR.parse_lrat(core["core_lrat"])
        self.assertEqual((variables, len(clauses)), (438, 2405))
        self.assertEqual((len(additions), deletions), (2007, 0))
        self.assertEqual(additions[max(additions)][0], ())

    def test_generation_is_byte_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as left, tempfile.TemporaryDirectory() as right:
            left_hashes = GENERATOR.generate(ROOT, Path(left))
            right_hashes = GENERATOR.generate(ROOT, Path(right))
            self.assertEqual(left_hashes, right_hashes)
            self.assertEqual(len(left_hashes), 82)

    def test_corrupted_frozen_input_is_rejected(self) -> None:
        source = ROOT / GENERATOR.SOURCE_REL
        with tempfile.TemporaryDirectory() as temporary:
            copied = Path(temporary)
            for name in GENERATOR.EXPECTED:
                (copied / name).write_bytes((source / name).read_bytes())
            data = bytearray((copied / "formula.cnf").read_bytes())
            data[-2] ^= 1
            (copied / "formula.cnf").write_bytes(data)
            with self.assertRaisesRegex(ValueError, "frozen input hash mismatch"):
                GENERATOR.read_frozen(copied, "formula.cnf")


if __name__ == "__main__":
    unittest.main()
