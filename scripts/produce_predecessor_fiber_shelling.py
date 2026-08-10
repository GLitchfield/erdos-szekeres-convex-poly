#!/usr/bin/env python3
"""Falsify an endpoint-indexed predecessor-fiber Boolean shelling.

Frozen mathematical specification
=================================

Fix ``k`` and put ``d = k - 2``.  For a triple coloring, an endpoint ``v``,
a predecessor ``u < v``, a turn color ``c``, and ``0 <= r < d``, put ``u``
in ``F_c(v, r)`` exactly when a ``c``-colored consecutive chain of at least
``r + 2`` vertices ends in the ordered pair ``(u, v)``.  Equivalently, the
pair rank used by ``ErdosSzekeres.RankProfile`` is at least ``r + 1``.

A map ``label`` from vertices to subsets of ``{0, ..., d - 1}`` is
*shell-coherent* when every exclusive predecessor-fiber event is oriented by
the corresponding Boolean coordinate:

* if ``u`` is in ``F_left(v, r)`` but not ``F_right(v, r)``, coordinate ``r``
  is absent from ``label(u)`` and present in ``label(v)``;
* if ``u`` is in ``F_right(v, r)`` but not ``F_left(v, r)``, coordinate ``r``
  is present in ``label(u)`` and absent from ``label(v)``;
* membership in both fibers, or neither fiber, imposes no condition.

This specification is frozen independently of the conjectural property being
tested.  In particular, shell coherence does not mention injectivity, a
cardinality bound, a power of two, or a strong-polygon conclusion.  The
separate experimental question is whether a target-free recursively
decomposable coloring admits an injective shell-coherent labeling.

This producer imports the previously frozen decomposable-coloring enumerator.
The independent checker imports neither producer nor enumerator and recomputes
pair ranks by exhaustive chain enumeration rather than this file's dynamic
program.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import platform
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import TypeAlias

from enumerate_decomposable_colorings import (
    Tree,
    enumerate_colorings,
    is_signotope,
    is_strong,
    tree_json,
    triples,
)


Ranks: TypeAlias = dict[tuple[int, int], tuple[int, int]]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return completed.stdout.strip()


def turn(bits: int, positions: dict[tuple[int, int, int], int],
         a: int, b: int, c: int) -> bool:
    return bool(bits & (1 << positions[(a, b, c)]))


def pair_ranks(bits: int, n: int, clip: int,
               positions: dict[tuple[int, int, int], int]) -> Ranks:
    """Compute clipped (right/cap, left/cup) consecutive pair ranks."""
    ranks: Ranks = {}
    for v in range(n):
        for u in range(v):
            right = left = 1
            for w in range(u):
                old_right, old_left = ranks[(w, u)]
                if turn(bits, positions, w, u, v):
                    left = max(left, min(clip, old_left + 1))
                else:
                    right = max(right, min(clip, old_right + 1))
            ranks[(u, v)] = right, left
    return ranks


def force_bit(fixed: list[dict[int, int]], vertex: int, coordinate: int,
              value: int, reasons: list[list[dict[str, object]]],
              reason: dict[str, object]) -> None:
    fixed[vertex].setdefault(coordinate, value)
    reasons[vertex].append(reason)
    if fixed[vertex][coordinate] != value:
        fixed[vertex][coordinate] = -1


def shell_constraints(ranks: Ranks, n: int, clip: int) -> tuple[
        list[dict[int, int]], list[list[dict[str, object]]]]:
    fixed: list[dict[int, int]] = [dict() for _ in range(n)]
    reasons: list[list[dict[str, object]]] = [[] for _ in range(n)]
    for (u, v), (right_rank, left_rank) in sorted(ranks.items()):
        for coordinate in range(clip):
            threshold = coordinate + 1
            in_left = left_rank >= threshold
            in_right = right_rank >= threshold
            if in_left == in_right:
                continue
            if in_left:
                assignments = ((u, 0), (v, 1))
                color = "left"
            else:
                assignments = ((u, 1), (v, 0))
                color = "right"
            for vertex, value in assignments:
                force_bit(
                    fixed,
                    vertex,
                    coordinate,
                    value,
                    reasons,
                    {
                        "pair": [u, v],
                        "coordinate": coordinate,
                        "exclusive_color": color,
                        "right_rank": right_rank,
                        "left_rank": left_rank,
                        "forced_vertex": vertex,
                        "forced_value": value,
                    },
                )
    return fixed, reasons


def allowed_labels(fixed: list[dict[int, int]], clip: int) -> list[list[int]]:
    answers: list[list[int]] = []
    for constraints in fixed:
        if any(value not in (0, 1) for value in constraints.values()):
            answers.append([])
            continue
        labels = []
        for label in range(1 << clip):
            if all(((label >> coordinate) & 1) == value
                   for coordinate, value in constraints.items()):
                labels.append(label)
        answers.append(labels)
    return answers


def injective_matching(allowed: list[list[int]]) -> list[int] | None:
    owner: dict[int, int] = {}

    def augment(vertex: int, seen: set[int]) -> bool:
        for label in allowed[vertex]:
            if label in seen:
                continue
            seen.add(label)
            previous = owner.get(label)
            if previous is None or augment(previous, seen):
                owner[label] = vertex
                return True
        return False

    for vertex in sorted(range(len(allowed)), key=lambda v: len(allowed[v])):
        if not augment(vertex, set()):
            return None
    matching = [-1] * len(allowed)
    for label, vertex in owner.items():
        matching[vertex] = label
    assert all(label >= 0 for label in matching)
    return matching


def first_hall_witness(allowed: list[list[int]]) -> tuple[list[int], list[int]]:
    n = len(allowed)
    for size in range(1, n + 1):
        for vertices in itertools.combinations(range(n), size):
            neighbors = sorted({label for vertex in vertices for label in allowed[vertex]})
            if len(neighbors) < len(vertices):
                return list(vertices), neighbors
    raise AssertionError("a failed bipartite matching must have a Hall witness")


def target_free(bits: int, n: int, k: int,
                positions: dict[tuple[int, int, int], int]) -> bool:
    if n < k:
        return True
    return not any(
        is_strong(bits, positions, vertices)
        for vertices in itertools.combinations(range(n), k)
    )


def encode_constraints(fixed: list[dict[int, int]]) -> list[dict[str, int]]:
    return [
        {str(coordinate): value for coordinate, value in sorted(row.items())}
        for row in fixed
    ]


def find_failure() -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    tested = Counter()
    target_free_count = 0
    signotope_count = 0

    # Increasing k, then support size, then coloring integer is the frozen
    # search order.  The first decisive exact failure terminates the search.
    for k in range(5, 9):
        clip = k - 2
        for n in range(1, 9):
            colorings, _ = enumerate_colorings(n)
            triple_list = triples(n)
            positions = {triple: index for index, triple in enumerate(triple_list)}
            width = max(1, (len(triple_list) + 3) // 4)
            for bits, tree in sorted(colorings.items()):
                tested[f"k={k},n={n}"] += 1
                if not target_free(bits, n, k, positions):
                    continue
                target_free_count += 1
                signotope_count += int(is_signotope(bits, positions, n))
                ranks = pair_ranks(bits, n, clip, positions)
                fixed, reasons = shell_constraints(ranks, n, clip)
                allowed = allowed_labels(fixed, clip)
                matching = injective_matching(allowed)
                if matching is not None:
                    continue
                hall_vertices, hall_labels = first_hall_witness(allowed)
                relevant_reasons = {
                    str(vertex): reasons[vertex]
                    for vertex in hall_vertices
                }
                producer = Path(__file__).resolve()
                return {
                    "schema_version": 1,
                    "status": "refuted",
                    "generation_base_revision": git_revision(repo),
                    "producer": "scripts/produce_predecessor_fiber_shelling.py",
                    "producer_sha256": file_sha256(producer),
                    "frozen_inputs": {
                        "ErdosSzekeres/RankProfile.lean": (
                            "e11868a7779e78b7bb2c58dadb9dddf53dd128e47f4a5c4b507a43ae44656f05"
                        ),
                        "scripts/enumerate_decomposable_colorings.py": (
                            "25edc9925ef9f79c1ed1c0dd3e03c419df418a1cda3da1dbeac7fa080f1a1f1f"
                        ),
                        "scripts/check_decomposable_enumeration.py": (
                            "2b16e231d388c33aefca396c3c49ef4991c2a662fc7a67e9961fe63a15107405"
                        ),
                        "docs/experiments/0079-state-578-blocker-consumer.md": (
                            "8f871cb08ffedfa308acfb94bf9ad1f07b80f9e6b65807921930e868b395eb0c"
                        ),
                    },
                    "runtime": {
                        "python": sys.version,
                        "platform": platform.platform(),
                        "resource_ceiling": {
                            "wall_minutes_per_computation": 30,
                            "cpu_cores": 4,
                            "memory_gib": 6,
                            "output_gib": 1.5,
                        },
                    },
                    "frozen_specification": {
                        "coordinate_count": "d = k - 2",
                        "fiber": (
                            "F_c(v,r) contains u<v iff the c-colored consecutive "
                            "pair rank at (u,v) is at least r+1"
                        ),
                        "exclusive_left": "force label(u)[r]=0 and label(v)[r]=1",
                        "exclusive_right": "force label(u)[r]=1 and label(v)[r]=0",
                        "tie": "both or neither imposes no constraint",
                        "separate_test": "existence of an injective coherent labeling",
                        "noncircularity": (
                            "coherence does not mention injectivity, cardinality, "
                            "a power of two, or a target conclusion"
                        ),
                    },
                    "scope": {
                        "search_order": "k=5..8, then n=1..8, then coloring integer",
                        "tested_object_class": "recursively decomposable triple coloring",
                        "arbitrary_coloring": False,
                        "signotope": True,
                        "signotope_check": "direct one-change computation",
                        "swept_realization": True,
                        "swept_realization_basis": (
                            "external compiling theorem IsDecomposable.isSweepRealizable; "
                            "not geometrically replayed by this certificate"
                        ),
                        "target_free": True,
                    },
                    "coverage_before_stop": {
                        "colorings_visited": dict(sorted(tested.items())),
                        "target_free_colorings_tested": target_free_count,
                        "signotopes_among_target_free": signotope_count,
                    },
                    "failure": {
                        "k": k,
                        "n": n,
                        "clip": clip,
                        "coloring_hex": f"{bits:0{width}x}",
                        "triple_order": (
                            "lexicographic combinations(range(n),3); LSB first; 1=left"
                        ),
                        "tree": tree_json(tree),
                        "pair_ranks": [
                            {
                                "u": u,
                                "v": v,
                                "right": rank[0],
                                "left": rank[1],
                            }
                            for (u, v), rank in sorted(ranks.items())
                        ],
                        "fixed_coordinates": encode_constraints(fixed),
                        "allowed_labels": allowed,
                        "hall_vertices": hall_vertices,
                        "hall_neighbor_labels": hall_labels,
                        "hall_defect": len(hall_vertices) - len(hall_labels),
                        "relevant_forcing_events": relevant_reasons,
                    },
                    "pascal_layers": {
                        str(layer): {
                            "boolean_lattice_capacity": __import__("math").comb(clip, layer),
                            "hall_neighbor_count_in_layer": sum(
                                label.bit_count() == layer for label in hall_labels
                            ),
                        }
                        for layer in range(clip + 1)
                    },
                    "claim_level": "computational_evidence",
                    "supported_claim": (
                        "the frozen predecessor-fiber shell-coherence candidate has an "
                        "exact target-free decomposable counterexample"
                    ),
                    "unsupported_claims": [
                        "the exact Erdos--Szekeres formula is false",
                        "all endpoint-indexed Boolean labelings are impossible",
                        "state 578 is false",
                    ],
                    "next_lean_target": (
                        "A kernel-reducible finite theorem for the displayed coloring: "
                        "the exclusive fiber constraints imply the recorded Hall defect."
                    ),
                }
    raise RuntimeError("no failure in the frozen k=5..8, n<=8 range")


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "output",
        type=Path,
        nargs="?",
        default=Path("data/derived/e3-predecessor-fiber-shelling-k8.json"),
    )
    args = parser.parse_args()
    write_atomic(args.output, find_failure())
    print(args.output)


if __name__ == "__main__":
    main()
