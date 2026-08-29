import importlib.util
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "extract_lrat_dependency_core", ROOT / "scripts/extract_lrat_dependency_core.py"
)
EXTRACTOR = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(EXTRACTOR)


class LRATDependencyCoreTest(unittest.TestCase):
    def test_deletion_rows_are_ignored_and_core_is_dense(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cnf = root / "tiny.cnf"
            lrat = root / "tiny.lrat"
            output = root / "core"
            cnf.write_text("p cnf 2 3\n1 0\n-1 2 0\n-2 0\n")
            lrat.write_text("4 2 0 2 1 0\n5 d 2 0\n6 0 4 3 0\n")
            metadata = EXTRACTOR.extract(cnf, lrat, output)
            self.assertEqual(metadata["source"]["deletion_lines"], 1)
            self.assertEqual(metadata["core"]["base_clauses"], 3)
            self.assertEqual(metadata["core"]["additions"], 2)
            self.assertEqual(output.joinpath("core.cnf").read_text(), cnf.read_text())
            self.assertEqual(
                output.joinpath("core.lrat").read_text(),
                "4 2 0 2 1 0\n5 0 4 3 0\n",
            )


if __name__ == "__main__":
    unittest.main()
