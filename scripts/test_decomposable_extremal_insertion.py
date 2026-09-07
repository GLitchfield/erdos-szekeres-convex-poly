"""Cross-check insertion search against exhaustive convex hull enumeration."""
from fractions import Fraction
import itertools
import random
import unittest

import baek_balko_constructions as bb
import decomposable_extremal_insertion as probe


class InsertionProbeTest(unittest.TestCase):
    def test_dynamic_program_against_exhaustive_hulls(self):
        rng = random.Random(20260907)
        for n in range(4, 10):
            for _ in range(4):
                while True:
                    points = [(i, rng.randrange(-100, 101)) for i in range(n)]
                    if bb.general_position(points):
                        break
                for k in range(4, n + 1):
                    expected = any(len(probe.hull_indices(points, s)) == k
                                   for s in itertools.combinations(range(n), k))
                    witness = probe.convex_witness(points, k)
                    self.assertEqual(witness is not None, expected, (points, k))

    def test_fibers_are_strict_and_cover_every_sweep_gap(self):
        points = sorted(bb.es_set3(4, 4, 4))
        candidates = list(probe.insertion_candidates(points, 0))
        self.assertEqual({gap for gap, _, _, _ in candidates}, set(range(5)))
        for gap, cell, count, q in candidates:
            self.assertTrue(bb.general_position(points + [q]))
            self.assertTrue(bb.distinct_x(points + [q]))
            self.assertEqual(sum(p[0] < q[0] for p in points), gap)
            self.assertLess(cell, count)
            witness = probe.convex_witness(points + [q], 4)
            self.assertIsNotNone(witness)
            self.assertIn(4, witness)

    def test_independent_hull_rejects_interior_vertex(self):
        points = [(Fraction(0), Fraction(0)), (Fraction(4), Fraction(0)),
                  (Fraction(1), Fraction(4)), (Fraction(1), Fraction(1))]
        self.assertEqual(len(probe.hull_indices(points, range(4))), 3)
        self.assertIsNone(probe.convex_witness(points, 4))

    def test_insertion_can_require_vertices_from_both_sweep_halves(self):
        # The larger half has three vertices (> 2^(4-3)), but adding q to
        # that half gives no quadrilateral. An endpoint-only insertion
        # argument would miss the quadrilateral that uses the smaller half.
        points = [(Fraction(0), Fraction(1)),
                  (Fraction(7, 8), Fraction(31, 8)),
                  (Fraction(9, 8), Fraction(33, 8)),
                  (Fraction(2), Fraction(16))]
        q = (Fraction(7, 16), Fraction(-695, 112))
        self.assertTrue(bb.general_position(points + [q]))
        self.assertIsNotNone(probe.decomposition_tree(points))
        self.assertEqual(len(probe.hull_indices(points, range(4))), 3)
        self.assertIsNone(probe.convex_witness(points, 4))
        larger = [p for p in points if q[0] < p[0]] + [q]
        self.assertEqual(len(larger), 4)
        self.assertEqual(len(probe.hull_indices(larger, range(4))), 3)
        self.assertIsNone(probe.convex_witness(larger, 4))
        witness = probe.convex_witness(points + [q], 4)
        self.assertIsNotNone(witness)
        self.assertIn(4, witness)
        self.assertTrue(any(points[i][0] < q[0] for i in witness if i < 4))
        self.assertTrue(any(q[0] < points[i][0] for i in witness if i < 4))


if __name__ == '__main__':
    unittest.main()
