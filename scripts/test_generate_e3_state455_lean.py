#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path

from generate_e3_state455_lean import CHUNK_COUNT, write_encoding, write_modules


class State455GeneratorTest(unittest.TestCase):
    def test_generates_complete_bounded_hierarchy(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            write_encoding(directory)
            clauses, chunks = write_modules(directory)

            self.assertEqual(clauses, 1134)
            self.assertEqual(chunks, CHUNK_COUNT)
            encoding = (directory / "E3State455Encoding.lean").read_text()
            self.assertIn("e3State455_isCap_finFour_iff", encoding)
            self.assertIn("e3State455_isCup_finFive_iff", encoding)
            self.assertIn("e3State455_isStrongPolygonOn_finFive_iff", encoding)
            root = (directory / "E3State455CNFGenerated.lean").read_text()
            self.assertEqual(root.count("public import ErdosSzekeres.E3State455CNFChunk"), 8)
            self.assertIn("theorem e3State455CNF_unsat", root)
            self.assertIn("theorem e3State455CNF_of_constraints", root)


if __name__ == "__main__":
    unittest.main()
