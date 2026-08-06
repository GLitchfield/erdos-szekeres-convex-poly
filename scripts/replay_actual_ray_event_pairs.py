#!/usr/bin/env python3
"""Independently replay the frozen marked child-ray event obstruction."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from check_allocated_span_pascal_demand import Replay, file_sha256


Tree = int | tuple["Tree", "Tree"]

LOWER_TREE: Tree = ((8, (2, 1)), ((4, 7), 10))
UPPER_TREE: Tree = (((0, 3), ((6, 9), 5)), 11)
TREE: Tree = (LOWER_TREE, UPPER_TREE)
FRONTIER = ((0, 4), (2, 5), (4, 6), (5, 7), (6, 10), (8, 11))
RANK = 3
STRONG_SIZE = 7

Event = tuple[str, int, int, int]


def tree_vertices(tree: Tree) -> tuple[int, ...]:
    if isinstance(tree, int):
        return (tree,)
    return tuple(sorted(tree_vertices(tree[0]) + tree_vertices(tree[1])))


def tree_bits(tree: Tree, machine: Replay) -> int:
    if isinstance(tree, int):
        return 0
    left, right = tree
    vertices = tree_vertices(tree)
    left_vertices = tree_vertices(left)
    support = sum(1 << vertex for vertex in vertices)
    lower = sum(1 << vertex for vertex in left_vertices)
    return tree_bits(left, machine) | tree_bits(right, machine) | machine.crossing(
        support, lower
    )


def event_json(event: Event) -> list[object]:
    direction, start, finish, mark = event
    return [direction, [start, finish], mark]


def frozen_record() -> dict[str, object]:
    machine = Replay(12, STRONG_SIZE)
    bits = tree_bits(TREE, machine)
    support = sum(1 << vertex for vertex in tree_vertices(TREE))
    lower = sum(1 << vertex for vertex in tree_vertices(LOWER_TREE))
    upper_vertices = tree_vertices(UPPER_TREE)
    chains = tuple(itertools.combinations(upper_vertices, RANK - 1))
    universe: tuple[Event, ...] = tuple(
        (direction, start, finish, mark)
        for direction in ("left", "right")
        for start, finish in chains
        for mark in (start, finish)
    )

    def incident(span: tuple[int, int], event: Event) -> bool:
        left, right = span
        direction, start, finish, _ = event
        if lower & (1 << left):
            return direction == "left" and left < start and finish == right
        return direction == "right" and start == left and finish < right

    supports = tuple(
        frozenset(event for event in universe if incident(span, event))
        for span in FRONTIER
    )
    chain_sets = []
    for support_events in supports:
        chain_ids = {(event[0], event[1], event[2]) for event in support_events}
        if len(chain_ids) != 1:
            raise AssertionError("independent replay lost unique frozen chain")
        direction, start, finish = next(iter(chain_ids))
        chain_sets.append(
            frozenset(
                (direction, start, finish, mark) for mark in (start, finish)
            )
        )
    selected = tuple(chain_sets)
    difference = sorted(supports[1] - supports[2])
    if not difference:
        raise AssertionError("adjacent support difference disappeared")

    absent_card = STRONG_SIZE - RANK - 1
    first_obstruction = None
    for later in range(len(FRONTIER)):
        available = set(universe) - supports[later]
        prior = selected[:later]
        missing = [index for index, present in enumerate(prior) if not present & available]
        disjoint = all(
            prior[i].isdisjoint(prior[j])
            for i in range(len(prior))
            for j in range(i + 1, len(prior))
        )
        if missing or (disjoint and len(prior) > absent_card):
            first_obstruction = {
                "later_index": later,
                "later_span": list(FRONTIER[later]),
                "prior_indices": list(range(later)),
                "prior_present_sets": [
                    [event_json(event) for event in sorted(present)]
                    for present in prior
                ],
                "all_prior_events_nonincident_later": not missing,
                "missing_prior_indices": missing,
                "prior_present_sets_pairwise_disjoint": disjoint,
                "required_hits": len(prior) if disjoint else None,
                "absent_card": absent_card,
            }
            break
    if first_obstruction is None:
        raise AssertionError("independent event replay unexpectedly passed")

    return {
        "maximum_n": 12,
        "strong_size": STRONG_SIZE,
        "rank": RANK,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "upper_vertices": list(upper_vertices),
        "frontier": [list(span) for span in FRONTIER],
        "active_supports": [
            [event_json(event) for event in sorted(support_events)]
            for support_events in supports
        ],
        "unique_present_sets": [
            [event_json(event) for event in sorted(present)]
            for present in selected
        ],
        "adjacent_pair": {
            "earlier": list(FRONTIER[1]),
            "later": list(FRONTIER[2]),
            "support_difference": [event_json(event) for event in difference],
            "passes": True,
        },
        "exact_size_skew_selection_exists": False,
        "first_obstruction": first_obstruction,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported schema")
    repo = Path(__file__).resolve().parent.parent
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise AssertionError(f"source hash mismatch: {source['path']}")
    replay = frozen_record()
    if replay != manifest["frozen_n12_k7"]:
        raise AssertionError("independent ray-event replay differs")
    obstruction = replay["first_obstruction"]
    print(
        "adjacent_pair_passes=",
        replay["adjacent_pair"]["passes"],
        "first_obstruction_later_index=",
        obstruction["later_index"],
        "required_hits=",
        obstruction["required_hits"],
        "absent_card=",
        obstruction["absent_card"],
    )


if __name__ == "__main__":
    main()
