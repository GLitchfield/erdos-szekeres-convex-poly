#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import check_two_root_span_footprints as checker
import enumerate_two_root_span_footprints as producer


class TwoRootSpanFootprintTest(unittest.TestCase):
    def test_independent_small_replay(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            manifest = producer.produce(5, 5, 1, Path(temporary))
            actual = checker.replay(manifest, 1)
        expected_contexts = [
            {key: value for key, value in context.items() if key != "machine_file"}
            for context in manifest["contexts"]
        ]
        self.assertEqual(actual["contexts"], expected_contexts)
        self.assertEqual(actual["summary"], manifest["summary"])
        self.assertEqual(manifest["parameters"]["context_count"], 42)
        self.assertEqual(manifest["parameters"]["interleaved_context_count"], 38)
        self.assertEqual(manifest["summary"]["total_transition_collision_count"], 0)


if __name__ == "__main__":
    unittest.main()
