#!/usr/bin/env python3
"""Specification-first tests for the rank-profile dynamic program."""

from __future__ import annotations

import itertools
import unittest

import analyze_decomposable_rank_profiles as analyzer


def direct_states(bits: int, vertices: tuple[int, ...], clip: int):
    """Enumerate chains directly, without the producer's rank recurrence."""
    ranks = {}
    downsets = []
    for v_position, v in enumerate(vertices):
        incoming = []
        for u_position, u in enumerate(vertices[:v_position]):
            best = [1, 1]
            for size in range(u_position + 1):
                for prefix in itertools.combinations(vertices[:u_position], size):
                    chain = prefix + (u, v)
                    for color in (False, True):
                        if all(
                            analyzer.turn(bits, *chain[index:index + 3]) == color
                            for index in range(len(chain) - 2)
                        ):
                            best[int(color)] = max(
                                best[int(color)], min(clip, len(chain) - 1))
            ranks[(u, v)] = best[0], best[1]
            incoming.append(ranks[(u, v)])
        mask = 0
        for false_rank, true_rank in incoming:
            for a in range(false_rank):
                for b in range(true_rank):
                    mask |= 1 << (clip * a + b)
        downsets.append(mask)
    return (
        tuple(downsets),
        tuple(ranks[pair] for pair in itertools.combinations(vertices, 2)),
    )


class RankProfileSemanticsTests(unittest.TestCase):
    def test_dynamic_program_equals_direct_chain_maximum(self):
        for n in range(2, 6):
            vertices = tuple(range(n))
            local_triples = tuple(itertools.combinations(vertices, 3))
            for local_bits in range(1 << len(local_triples)):
                bits = sum(
                    ((local_bits >> index) & 1)
                    << analyzer.POSITIONS[triple]
                    for index, triple in enumerate(local_triples)
                )
                for clip in range(1, 6):
                    with self.subTest(n=n, coloring=local_bits, clip=clip):
                        self.assertEqual(
                            analyzer.rank_states(bits, vertices, clip),
                            direct_states(bits, vertices, clip),
                        )


if __name__ == "__main__":
    unittest.main()
