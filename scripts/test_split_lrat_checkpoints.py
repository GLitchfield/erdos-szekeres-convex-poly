#!/usr/bin/env python3

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from split_lrat_checkpoints import (
    parse_addition,
    parse_bundle_size_overrides,
    segment_at,
    write_context_module,
    write_segment_module,
)


class SplitLratCheckpointsTest(unittest.TestCase):
    def test_segment_at_uses_byte_intervals(self) -> None:
        self.assertEqual(segment_at(0, 100, 4), 0)
        self.assertEqual(segment_at(24, 100, 4), 0)
        self.assertEqual(segment_at(25, 100, 4), 1)
        self.assertEqual(segment_at(99, 100, 4), 3)

    def test_parse_addition_separates_literals_and_references(self) -> None:
        self.assertEqual(
            parse_addition(b"12 -1 3 0 4 -9 0\n", 0),
            (12, [b"-1", b"3"], [4, 9]),
        )

    def test_parse_addition_ignores_deletions(self) -> None:
        self.assertIsNone(parse_addition(b"12 d 3 4 0\n", 0))

    def test_parse_addition_rejects_unterminated_lines(self) -> None:
        with self.assertRaisesRegex(ValueError, "byte 17"):
            parse_addition(b"12 -1 0 3\n", 17)

    def test_context_excludes_checkpoint_projections_from_suggestions(self) -> None:
        with TemporaryDirectory() as temporary:
            path = Path(temporary) / "Context.lean"
            write_context_module(path, "ExampleCheckpoint", "example.cnf")
            source = path.read_text(encoding="utf-8")
        self.assertIn(
            'nameDenyListExt.addEntry env "ExampleCheckpoint"', source
        )
        self.assertIn("lrat_checkpoint_context ExampleCheckpointContext", source)

    def test_bundle_size_overrides_are_bounded_and_unique(self) -> None:
        self.assertEqual(
            parse_bundle_size_overrides(["99:4096", "7:512"], 100),
            {99: 4096, 7: 512},
        )
        with self.assertRaisesRegex(ValueError, "out of range"):
            parse_bundle_size_overrides(["100:4096"], 100)
        with self.assertRaisesRegex(ValueError, "duplicate"):
            parse_bundle_size_overrides(["7:512", "7:256"], 100)

    def test_compact_final_uses_private_endpoint_command(self) -> None:
        with TemporaryDirectory() as temporary:
            path = Path(temporary) / "Segment003.lean"
            write_segment_module(
                path,
                "ExampleCheckpoint",
                3,
                4096,
                "ExampleCheckpointContext",
                ["ExampleCheckpointSegment002"],
                "example.cnf",
                "segment.lrat",
                "carry-input.txt",
                "carry-output.txt",
                compact_final=True,
            )
            source = path.read_text(encoding="utf-8")
        self.assertIn("public import ErdosSzekeres.LRATCheckpointFinal", source)
        self.assertIn("lrat_checkpoint_final_segment", source)


if __name__ == "__main__":
    unittest.main()
