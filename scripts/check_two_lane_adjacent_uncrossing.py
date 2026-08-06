#!/usr/bin/env python3
"""Produce the frozen adjacent meet/join uncrossing gate.

The two reflected endpoint lanes remain subsets of the existing untagged
ideal lattice.  This gate first refutes the rigid convention that meet must
remain with the earlier span and join with the later span.  It then tests the
weaker local rule allowing either assignment of meet and join, provided both
new ideals remain in the respective two-lane unions.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    DecomposableColorings,
    LocalSpanAnalysis,
    context_groups,
    endpoint_transition_candidates,
    file_sha256,
    git_revision,
    write_atomic,
)
from enumerate_reflected_transition_hall import (
    FROZEN_LOWER_TREE,
    FROZEN_TREE,
    oriented_candidates,
    tree_coloring_bits,
    tree_support,
)


def pair_example(
    group_index: int,
    adjacent_index: int,
    frontier: tuple[tuple[int, int], ...],
    first: int,
    second: int,
) -> dict[str, object]:
    return {
        "group_index": group_index,
        "adjacent_index": adjacent_index,
        "earlier_span": list(frontier[adjacent_index]),
        "later_span": list(frontier[adjacent_index + 1]),
        "earlier_ideal_hex": f"{first:x}",
        "later_ideal_hex": f"{second:x}",
        "meet_hex": f"{first & second:x}",
        "join_hex": f"{first | second:x}",
    }


def frozen_record() -> dict[str, object]:
    maximum_n = 12
    strong_size = 7
    colorings = DecomposableColorings(maximum_n)
    analyzer = LocalSpanAnalysis(maximum_n, strong_size)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, colorings)
    local = analyzer.analyze(bits, support)
    if local is None:
        raise AssertionError("frozen root unexpectedly contains a strong seven")
    support_vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    records = []
    first_forward_failure = None
    first_flexible_failure = None
    total_pairs = 0
    for group_index, (color, rank, frontier) in enumerate(
        context_groups(local, support, lower, maximum_n)
    ):
        original, _, _, _ = endpoint_transition_candidates(
            local, support_vertices, frontier, color, rank, strong_size
        )
        candidates = oriented_candidates(
            original,
            frontier,
            lower,
            rank - 1,
            strong_size - rank - 1,
        )
        adjacent_records = []
        for adjacent_index in range(len(frontier) - 1):
            earlier = set(candidates[adjacent_index])
            later = set(candidates[adjacent_index + 1])
            forward_count = 0
            reverse_count = 0
            both_count = 0
            pair_count = len(earlier) * len(later)
            total_pairs += pair_count
            local_forward_failure = None
            local_flexible_failure = None
            for first in sorted(earlier):
                for second in sorted(later):
                    meet = first & second
                    join = first | second
                    forward = meet in earlier and join in later
                    reverse = join in earlier and meet in later
                    forward_count += int(forward)
                    reverse_count += int(reverse)
                    both_count += int(forward and reverse)
                    example = pair_example(
                        group_index, adjacent_index, frontier, first, second
                    )
                    if not forward and local_forward_failure is None:
                        local_forward_failure = example
                    if not (forward or reverse) and local_flexible_failure is None:
                        local_flexible_failure = example
            if first_forward_failure is None and local_forward_failure is not None:
                first_forward_failure = local_forward_failure
            if first_flexible_failure is None and local_flexible_failure is not None:
                first_flexible_failure = local_flexible_failure
            adjacent_records.append(
                {
                    "adjacent_index": adjacent_index,
                    "earlier_span": list(frontier[adjacent_index]),
                    "later_span": list(frontier[adjacent_index + 1]),
                    "candidate_pair_count": pair_count,
                    "forward_valid_count": forward_count,
                    "reverse_valid_count": reverse_count,
                    "both_valid_count": both_count,
                    "fixed_forward_all": local_forward_failure is None,
                    "flexible_either_all": local_flexible_failure is None,
                    "first_forward_failure": local_forward_failure,
                    "first_flexible_failure": local_flexible_failure,
                }
            )
        records.append(
            {
                "color": "cup" if color else "cap",
                "rank": rank,
                "frontier": [list(span) for span in frontier],
                "candidate_families_hex": [
                    [f"{ideal:x}" for ideal in family] for family in candidates
                ],
                "adjacent_pairs": adjacent_records,
            }
        )
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(records),
        "candidate_pair_checks": total_pairs,
        "groups": records,
        "fixed_forward_all": first_forward_failure is None,
        "first_forward_failure": first_forward_failure,
        "flexible_either_all": first_flexible_failure is None,
        "first_flexible_failure": first_flexible_failure,
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_two_lane_adjacent_uncrossing.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-two-lane-adjacent-uncrossing-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "carrier": "existing untagged orientation-reflected ideal candidates",
            "fixed_forward": (
                "meet remains with the earlier span and join with the later span"
            ),
            "flexible_either": (
                "either the forward assignment or the reverse meet/join "
                "assignment preserves membership in the two candidate unions"
            ),
            "claim_boundary": (
                "bounded adjacent-pair gate only; no augmenting-path termination "
                "or general Hall conclusion"
            ),
        },
        "frozen_n12_k7": frozen_record(),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "base_producer": {
                "path": "scripts/enumerate_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/enumerate_allocated_span_pascal_demand.py"
                ),
            },
            "base_checker": {
                "path": "scripts/check_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/check_allocated_span_pascal_demand.py"
                ),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    write_atomic(args.output, produce(repo))
    print(args.output)


if __name__ == "__main__":
    main()
