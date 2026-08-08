#!/usr/bin/env python3
from __future__ import annotations

import itertools
import unittest

from generate_rooted_cup_blocks_state_sat import forced_root_units


class RootedCupBlocksStateSATTest(unittest.TestCase):
    def test_centered_root_units_encode_deep_below_crossings(self) -> None:
        triples = tuple(itertools.combinations(range(5), 3))
        variables = {triple: index + 1 for index, triple in enumerate(triples)}
        root, units = forced_root_units(2, 2, variables)
        self.assertEqual(root, 2)
        self.assertEqual(len(units), 6)
        expected = {
            (variables[triple] if triple[1] == root else -variables[triple])
            for triple in triples
            if root in triple
        }
        self.assertEqual({unit[0] for unit in units}, expected)
        self.assertEqual(sum(unit[0] > 0 for unit in units), 4)
        self.assertEqual(sum(unit[0] < 0 for unit in units), 2)


if __name__ == "__main__":
    unittest.main()
