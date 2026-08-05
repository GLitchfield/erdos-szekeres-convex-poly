#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import check_singleton_residuals as checker
import enumerate_singleton_residuals as producer


class SingletonResidualTest(unittest.TestCase):
    def test_independent_small_replay(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            manifest = producer.produce(5, 5, 1, Path(temporary))
            actual = checker.replay(manifest, 1)
        expected_contexts = [
            {key: value for key, value in item.items() if key != "machine_file"}
            for item in manifest["contexts"]
        ]
        self.assertEqual(actual["contexts"], expected_contexts)
        self.assertEqual(actual["summary"], manifest["summary"])
        self.assertEqual(manifest["summary"]["coloring_count"], 62)
        self.assertEqual(manifest["summary"]["child_observation_count"], 33)
        self.assertEqual(manifest["summary"]["residual_class_count"], 33)

    def test_record_difference_reports_the_first_gap(self) -> None:
        first = bytes((0,)) + (1).to_bytes(4, "little") + (0).to_bytes(4, "little")
        second = bytes((0,)) + (1).to_bytes(4, "little") + (2).to_bytes(4, "little")
        difference = producer.record_difference(first, second)
        self.assertEqual(difference["gap"], 1)
        self.assertEqual(difference["fields"], ["cup_anchor_left"])


if __name__ == "__main__":
    unittest.main()
