#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import check_span_rank_footprints as checker
import enumerate_span_rank_footprints as producer


class SpanRankFootprintTest(unittest.TestCase):
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
        self.assertEqual(manifest["summary"]["child_footprint_count"], 47)
        self.assertEqual(manifest["summary"]["total_transition_collision_count"], 0)
        self.assertEqual(
            manifest["summary"]["total_observation_readout_mismatch_count"], 0
        )


if __name__ == "__main__":
    unittest.main()
