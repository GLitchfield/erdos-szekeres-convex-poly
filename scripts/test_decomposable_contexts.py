#!/usr/bin/env python3
from __future__ import annotations

import unittest

import check_decomposable_contexts as checker
import enumerate_decomposable_contexts as producer


class DecomposableContextTest(unittest.TestCase):
    def test_profile_packing_and_restriction_order(self) -> None:
        small = producer.pack_profile([1, 2, 0, 3, 1, 0], False)
        large = producer.pack_profile([2, 2, 1, 4, 1, 3], True)
        self.assertEqual(producer.unpack_profile(small), (1, 2, 0, 3, 1, 0, 0))
        self.assertTrue(producer.profile_le(small, large))
        self.assertFalse(producer.profile_le(large, small))

    def test_independent_all_root_replay_at_five(self) -> None:
        manifest = producer.produce(5)
        replay = checker.replay(5)
        expected_profile = {
            key: manifest["profile"][key]
            for key in ("alphabet_size", "alphabet_sha256")
        }
        self.assertEqual(replay["profile"], expected_profile)
        self.assertEqual(replay["canonical_hashes"], manifest["canonical_hashes"])
        self.assertEqual(replay["layers"], manifest["layers"])

        layer = manifest["layers"]["5"]
        self.assertEqual(layer["distinct_coloring_count"], 62)
        self.assertEqual(layer["valid_root_count"], 120)
        self.assertGreater(layer["local_open_transition_collision_count"], 0)
        self.assertEqual(layer["all_gap_open_transition_collision_count"], 0)
        self.assertEqual(layer["endpoint_transition_violations"], 0)
        self.assertEqual(layer["saturation_violations"], 0)
        self.assertEqual(layer["restriction_violations"], 0)


if __name__ == "__main__":
    unittest.main()
