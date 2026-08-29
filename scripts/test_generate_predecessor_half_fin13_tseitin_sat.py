import importlib.util
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "generate_predecessor_half_fin13_tseitin_sat",
    ROOT / "scripts/generate_predecessor_half_fin13_tseitin_sat.py",
)
GENERATOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(GENERATOR)


class Fin13TseitinSATTest(unittest.TestCase):
    def test_dimensions_and_categories(self) -> None:
        entries = GENERATOR.annotated_formula()
        counts = {
            category: sum(entry["category"] == category for entry in entries)
            for category in {entry["category"] for entry in entries}
        }
        self.assertEqual(len(GENERATOR.TVAR), 286)
        self.assertEqual(len(GENERATOR.QVAR), 715)
        self.assertEqual(len(GENERATOR.FVAR), 1287)
        self.assertEqual(counts["one_change"], 5720)
        self.assertEqual(counts["strong_quad_definition"], 11440)
        self.assertEqual(counts["strong_five_definition"], 7722)
        self.assertEqual(counts["no_strong_six"], 1716)
        self.assertEqual(counts["every_seven_has_strong_five"], 1716)
        self.assertEqual(len(entries), 28314)


if __name__ == "__main__":
    unittest.main()
