import unittest

import check_allocated_span_pascal_demand as checker
import enumerate_allocated_span_pascal_demand as producer


class AllocatedSpanPascalDemandTest(unittest.TestCase):
    def test_small_all_root_replay(self) -> None:
        manifest = producer.produce(5, 6)
        actual = checker.replay(5, 6)
        self.assertEqual(actual["statistics"], manifest["statistics"])
        self.assertEqual(actual["rank_census"], manifest["rank_census"])
        self.assertEqual(
            actual["endpoint_projection_falsifier"],
            manifest["endpoint_projection_falsifier"],
        )
        self.assertEqual(
            actual["first_saturation_examples"],
            manifest["first_saturation_examples"],
        )
        self.assertEqual(
            actual["canonical_context_sha256"],
            manifest["canonical_context_sha256"],
        )
        self.assertIsNone(manifest["first_violation"])


if __name__ == "__main__":
    unittest.main()
