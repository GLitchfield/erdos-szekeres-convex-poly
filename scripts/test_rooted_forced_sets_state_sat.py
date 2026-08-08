#!/usr/bin/env python3
from __future__ import annotations

import itertools
import unittest

from generate_rooted_forced_sets_state_sat import forced_set_units, parse_vertex_set


class RootedForcedSetsStateSATTest(unittest.TestCase):
    def test_forced_cap_units_are_negative(self) -> None:
        triples = tuple(itertools.combinations(range(5), 3))
        variables = {triple: index + 1 for index, triple in enumerate(triples)}
        units = forced_set_units([(0, 1, 3, 4)], variables, False)
        self.assertEqual(len(units), 4)
        self.assertTrue(all(unit[0] < 0 for unit in units))

    def test_parse_vertex_set_sorts_vertices(self) -> None:
        self.assertEqual(parse_vertex_set("4,0,2", 5), (0, 2, 4))

    def test_parse_vertex_set_rejects_repetition(self) -> None:
        with self.assertRaises(Exception):
            parse_vertex_set("1,1,2", 5)


if __name__ == "__main__":
    unittest.main()
