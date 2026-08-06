from __future__ import annotations

import unittest

from enumerate_span_rank_footprints import SpanRankFootprint
from span_dominance_quotient import encode_span_dominance_quotient


class SpanDominanceQuotientTests(unittest.TestCase):
    def test_closed_records_have_one_terminal_encoding(self) -> None:
        footprint = SpanRankFootprint(6, 6)
        self.assertEqual(
            encode_span_dominance_quotient(footprint.closed_record, 6, 6),
            bytes((1,)),
        )

    def test_complementary_colorings_have_distinct_open_encodings(self) -> None:
        footprint = SpanRankFootprint(5, 6)
        triple_count = len(footprint.triples)
        all_cup = footprint.encode((1 << triple_count) - 1)
        all_cap = footprint.encode(0)
        self.assertNotEqual(
            encode_span_dominance_quotient(all_cup, 5, 6),
            encode_span_dominance_quotient(all_cap, 5, 6),
        )

    def test_record_length_is_checked(self) -> None:
        with self.assertRaisesRegex(ValueError, "record length"):
            encode_span_dominance_quotient(bytes((0, 0)), 5, 6)


if __name__ == "__main__":
    unittest.main()
