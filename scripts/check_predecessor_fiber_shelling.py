#!/usr/bin/env python3
"""Independently check a predecessor-fiber shelling counterexample.

This checker imports neither the producer nor the decomposable-coloring
enumerator.  It reconstructs the coloring by recursive tree descent and
computes consecutive-chain ranks by enumerating every possible prefix.  The
producer instead uses subset dynamic programming and a rank recurrence.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
from typing import TypeAlias


Tree: TypeAlias = int | tuple["Tree", "Tree"]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_tree(value: object) -> Tree:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    if not isinstance(value, dict) or set(value) != {"lower", "upper"}:
        raise ValueError("invalid decomposition tree")
    return parse_tree(value["lower"]), parse_tree(value["upper"])


def leaves(tree: Tree) -> frozenset[int]:
    if isinstance(tree, int):
        return frozenset((tree,))
    lower = leaves(tree[0])
    upper = leaves(tree[1])
    if lower & upper:
        raise ValueError("decomposition children overlap")
    return lower | upper


def tree_turn(tree: Tree, triple: tuple[int, int, int]) -> bool:
    if isinstance(tree, int):
        raise ValueError("a triple cannot lie in a leaf")
    lower_set = leaves(tree[0])
    upper_set = leaves(tree[1])
    selected = frozenset(triple)
    if selected <= lower_set:
        return tree_turn(tree[0], triple)
    if selected <= upper_set:
        return tree_turn(tree[1], triple)
    if not selected <= lower_set | upper_set:
        raise ValueError("triple is not supported by the tree")
    return triple[1] in lower_set


def reconstructed_bits(tree: Tree, n: int) -> tuple[int, tuple[tuple[int, int, int], ...]]:
    triples = tuple(itertools.combinations(range(n), 3))
    bits = sum(
        (1 << position) if tree_turn(tree, triple) else 0
        for position, triple in enumerate(triples)
    )
    return bits, triples


def turn(bits: int, positions: dict[tuple[int, int, int], int],
         a: int, b: int, c: int) -> bool:
    return bool(bits & (1 << positions[(a, b, c)]))


def direct_pair_rank(bits: int, positions: dict[tuple[int, int, int], int],
                     u: int, v: int, expected: bool, clip: int) -> int:
    """Enumerate all chain prefixes rather than applying a rank recurrence."""
    best = 1
    for size in range(u + 1):
        for prefix in itertools.combinations(range(u), size):
            chain = prefix + (u, v)
            if all(turn(bits, positions, *chain[index:index + 3]) == expected
                   for index in range(len(chain) - 2)):
                best = max(best, min(clip, len(chain) - 1))
    return best


def direct_pair_ranks(bits: int, n: int, clip: int,
                      positions: dict[tuple[int, int, int], int]) -> dict[
                          tuple[int, int], tuple[int, int]]:
    return {
        (u, v): (
            direct_pair_rank(bits, positions, u, v, False, clip),
            direct_pair_rank(bits, positions, u, v, True, clip),
        )
        for u, v in itertools.combinations(range(n), 2)
    }


def independent_constraints(ranks: dict[tuple[int, int], tuple[int, int]],
                            n: int, clip: int) -> tuple[
                                list[dict[int, int]], list[set[int]]]:
    fixed: list[dict[int, int]] = [dict() for _ in range(n)]
    contradictions: list[set[int]] = [set() for _ in range(n)]
    for (u, v), (right_rank, left_rank) in sorted(ranks.items()):
        for coordinate in range(clip):
            threshold = coordinate + 1
            left_only = left_rank >= threshold > right_rank
            right_only = right_rank >= threshold > left_rank
            if not left_only and not right_only:
                continue
            assignments = ((u, 0), (v, 1)) if left_only else ((u, 1), (v, 0))
            for vertex, value in assignments:
                previous = fixed[vertex].get(coordinate)
                if previous is not None and previous != value:
                    contradictions[vertex].add(coordinate)
                fixed[vertex][coordinate] = value
    return fixed, contradictions


def independent_allowed(fixed: list[dict[int, int]], contradictions: list[set[int]],
                        clip: int) -> list[list[int]]:
    return [
        [] if contradictions[vertex] else [
            label for label in range(1 << clip)
            if all(((label >> coordinate) & 1) == value
                   for coordinate, value in fixed[vertex].items())
        ]
        for vertex in range(len(fixed))
    ]


def has_injective_matching(allowed: list[list[int]]) -> bool:
    owner: dict[int, int] = {}

    def extend(vertex: int, used: set[int]) -> bool:
        for label in allowed[vertex]:
            if label in used:
                continue
            used.add(label)
            displaced = owner.get(label)
            if displaced is None or extend(displaced, used):
                owner[label] = vertex
                return True
        return False

    return all(
        extend(vertex, set())
        for vertex in sorted(range(len(allowed)), key=lambda x: len(allowed[x]))
    )


def is_strong(bits: int, positions: dict[tuple[int, int, int], int],
              vertices: tuple[int, ...]) -> bool:
    for a, b, c, d in itertools.combinations(vertices, 4):
        if turn(bits, positions, a, b, c) != turn(bits, positions, a, b, d):
            return False
        if turn(bits, positions, a, c, d) != turn(bits, positions, b, c, d):
            return False
    return True


def is_signotope(bits: int, positions: dict[tuple[int, int, int], int], n: int) -> bool:
    for a, b, c, d in itertools.combinations(range(n), 4):
        values = (
            turn(bits, positions, a, b, c),
            turn(bits, positions, a, b, d),
            turn(bits, positions, a, c, d),
            turn(bits, positions, b, c, d),
        )
        if sum(left != right for left, right in zip(values, values[1:])) > 1:
            return False
    return True


def normalize_constraints(fixed: list[dict[int, int]],
                          contradictions: list[set[int]]) -> list[dict[str, int]]:
    return [
        {
            str(coordinate): (-1 if coordinate in contradictions[vertex] else value)
            for coordinate, value in sorted(row.items())
        }
        for vertex, row in enumerate(fixed)
    ]


def run_controls() -> dict[str, bool]:
    # Positive: two unconstrained vertices have many distinct labels.
    positive = has_injective_matching([list(range(8)), list(range(8))])
    # Negative: two vertices sharing one singleton neighborhood violate Hall.
    negative = not has_injective_matching([[0], [0]])
    # A synthetic contradictory coordinate has no coherent label.
    contradictory = independent_allowed([{0: 0}], [{0}], 3) == [[]]
    return {
        "positive_unconstrained_matching": positive,
        "negative_singleton_hall_defect": negative,
        "negative_contradictory_coordinate": contradictory,
    }


def check(certificate_path: Path) -> dict[str, object]:
    certificate = json.loads(certificate_path.read_text())
    failure = certificate["failure"]
    n = failure["n"]
    k = failure["k"]
    clip = failure["clip"]
    tree = parse_tree(failure["tree"])
    bits, triples = reconstructed_bits(tree, n)
    positions = {triple: index for index, triple in enumerate(triples)}
    expected_bits = int(failure["coloring_hex"], 16)
    ranks = direct_pair_ranks(bits, n, clip, positions)
    recorded_ranks = {
        (row["u"], row["v"]): (row["right"], row["left"])
        for row in failure["pair_ranks"]
    }
    fixed, contradictions = independent_constraints(ranks, n, clip)
    allowed = independent_allowed(fixed, contradictions, clip)
    hall_vertices = failure["hall_vertices"]
    hall_neighbors = sorted({
        label for vertex in hall_vertices for label in allowed[vertex]
    })
    controls = run_controls()

    repo = Path(__file__).resolve().parent.parent
    producer_path = repo / certificate["producer"]
    input_hashes = {
        path: file_sha256(repo / path)
        for path in certificate["frozen_inputs"]
    }
    checks = {
        "schema": certificate.get("schema_version") == 1,
        "status_refuted": certificate.get("status") == "refuted",
        "base_revision": certificate.get("generation_base_revision")
            == "a02b121856132021caf0fc46c81577eda5400449",
        "producer_hash": file_sha256(producer_path) == certificate["producer_sha256"],
        "frozen_input_hashes": input_hashes == certificate["frozen_inputs"],
        "tree_support": leaves(tree) == frozenset(range(n)),
        "tree_coloring": bits == expected_bits,
        "direct_pair_ranks": ranks == recorded_ranks,
        "fixed_constraints": normalize_constraints(fixed, contradictions)
            == failure["fixed_coordinates"],
        "allowed_labels": allowed == failure["allowed_labels"],
        "target_free": n < k or not any(
            is_strong(bits, positions, vertices)
            for vertices in itertools.combinations(range(n), k)
        ),
        "signotope": is_signotope(bits, positions, n),
        "hall_neighbors": hall_neighbors == failure["hall_neighbor_labels"],
        "hall_defect": len(hall_vertices) - len(hall_neighbors)
            == failure["hall_defect"] > 0,
        "no_injective_matching": not has_injective_matching(allowed),
        "pascal_capacities": all(
            row["boolean_lattice_capacity"]
                == __import__("math").comb(clip, int(layer))
            for layer, row in certificate["pascal_layers"].items()
        ),
        "controls": all(controls.values()),
    }
    return {
        "certificate": str(certificate_path),
        "method": (
            "tree-descent coloring plus exhaustive chain-prefix ranks; "
            "imports neither producer nor prior enumerator"
        ),
        "object_class": {
            "arbitrary_coloring": False,
            "signotope_directly_checked": True,
            "recursively_decomposable_tree_directly_checked": True,
            "swept_realization": (
                "classified by external compiling theorem, not geometrically replayed here"
            ),
        },
        "controls": controls,
        "checks": checks,
        "ok": all(checks.values()),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "certificate",
        type=Path,
        nargs="?",
        default=Path("data/derived/e3-predecessor-fiber-shelling-k8.json"),
    )
    args = parser.parse_args()
    result = check(args.certificate)
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
