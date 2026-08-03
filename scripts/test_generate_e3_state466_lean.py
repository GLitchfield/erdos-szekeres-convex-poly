#!/usr/bin/env python3

import unittest

from generate_e3_state466_lean import balanced_chunks, balanced_join


class BalancedChunksTest(unittest.TestCase):
    def test_recombination_preserves_balanced_expression_tree(self) -> None:
        items = [str(index) for index in range(13)]
        chunks = balanced_chunks(items, 4)

        self.assertEqual([item for chunk in chunks for item in chunk], items)
        self.assertEqual(
            balanced_join([balanced_join(chunk, "∨") for chunk in chunks], "∨"),
            balanced_join(items, "∨"),
        )

    def test_rejects_nonbinary_chunk_count(self) -> None:
        with self.assertRaises(ValueError):
            balanced_chunks(["a", "b", "c"], 3)


if __name__ == "__main__":
    unittest.main()
