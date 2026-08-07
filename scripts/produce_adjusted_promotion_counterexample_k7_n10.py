#!/usr/bin/env python3
"""Produce the compact n=10 adjusted-promotion capacity counterexample.

This is a focused certificate producer, not an all-n search.  It reconstructs
the two reverse-comb children and their alternating root, checks openness and
the adjusted exact-rank groups with the producer-side interval implementation,
and records the first disproved Pascal layer.
"""

from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path

import enumerate_allocated_span_pascal_demand as base
import enumerate_rank_two_gap_promotion_k7 as promotion


Tree = int | tuple["Tree", "Tree"]

LOWER_TREE: Tree = ((((8, 4), 6), 2), 0)
UPPER_TREE: Tree = ((((9, 7), 5), 3), 1)
ROOT_TREE: Tree = (LOWER_TREE, UPPER_TREE)
EXPECTED_BITS = int("cde50debf387c0debf57f9c3e07f00", 16)
EXPECTED_SPANS = (
    (0, 2),
    (0, 3),
    (1, 4),
    (2, 4),
    (2, 5),
    (3, 6),
    (4, 6),
    (4, 7),
    (5, 8),
    (6, 8),
    (6, 9),
)


def boundary_slot(ideal: int, rows: int, columns: int) -> int:
    """Encode a cell-mask ideal by its boundary-step subset."""
    slot = 0
    row_mask = (1 << columns) - 1
    for row in range(rows):
        height = ((ideal >> (row * columns)) & row_mask).bit_count()
        slot |= 1 << (row + columns - height)
    return slot


def candidate_slots(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    span: tuple[int, int],
    color: int,
    rank: int,
    strong_size: int,
) -> set[int]:
    ideals = base.endpoint_transition_candidates(
        local, vertices, (span,), color, rank, strong_size
    )[0][0]
    rows = rank - 1
    columns = strong_size - rank - 1
    return {boundary_slot(ideal, rows, columns) for ideal in ideals}


def slot_family_mask(family: set[int]) -> str:
    return f"{sum(1 << slot for slot in family):08x}"


def exclusive_choice_graph(
    local: dict[tuple[int, int, int], int],
    support: int,
    lower: int,
    strong_size: int,
    groups: tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...],
    promotions: tuple[dict[str, object], ...],
) -> tuple[list[dict[str, object]], int, list[int], list[int]]:
    """Build and falsify the proposed one-charge-per-genealogy-source graph."""
    vertices = tuple(
        vertex for vertex in range(support.bit_length())
        if support & (1 << vertex)
    )
    charges: list[dict[str, object]] = []
    families: list[set[int]] = []

    for record in promotions:
        color = record["color"]
        rank = record["exact_ambient_rank"]
        gap = tuple(record["hidden_gap"])
        transition = tuple(record["matched_transition"])
        family = candidate_slots(
            local, vertices, gap, color, rank, strong_size
        ) | candidate_slots(
            local, vertices, transition, 1 - color, 2, strong_size
        )
        charges.append(
            {
                "kind": "hidden-source-exclusive-choice",
                "color": "cup" if color else "cap",
                "span": list(gap),
                "alternative_transition": list(transition),
                "candidate_slot_mask_hex": slot_family_mask(family),
            }
        )
        families.append(family)

    initial = (vertices[0], vertices[1])
    initial_family = (
        candidate_slots(local, vertices, initial, 0, 2, strong_size)
        | candidate_slots(local, vertices, initial, 1, 2, strong_size)
        | {0}
    )
    charges.append(
        {
            "kind": "initial-crossing-with-sentinel",
            "span": list(initial),
            "candidate_slot_mask_hex": slot_family_mask(initial_family),
        }
    )
    families.append(initial_family)

    for color, rank, spans in groups:
        if rank < 3:
            continue
        for span in spans:
            if bool(lower & (1 << span[0])) == bool(lower & (1 << span[1])):
                continue
            family = candidate_slots(
                local, vertices, span, color, rank, strong_size
            )
            charges.append(
                {
                    "kind": "higher-rank-crossing",
                    "color": "cup" if color else "cap",
                    "rank": rank,
                    "span": list(span),
                    "candidate_slot_mask_hex": slot_family_mask(family),
                }
            )
            families.append(family)

    matched: dict[int, int] = {}

    def augment(charge: int, seen: set[int]) -> bool:
        for slot in sorted(families[charge]):
            if slot in seen:
                continue
            seen.add(slot)
            if slot not in matched or augment(matched[slot], seen):
                matched[slot] = charge
                return True
        return False

    for charge in range(len(charges)):
        augment(charge, set())

    matched_charges = set(matched.values())
    reachable_charges = set(range(len(charges))) - matched_charges
    reachable_slots: set[int] = set()
    matched_edges = {(charge, slot) for slot, charge in matched.items()}
    changed = True
    while changed:
        changed = False
        for charge in tuple(reachable_charges):
            for slot in families[charge]:
                if (charge, slot) not in matched_edges and slot not in reachable_slots:
                    reachable_slots.add(slot)
                    changed = True
        for slot in tuple(reachable_slots):
            if slot in matched and matched[slot] not in reachable_charges:
                reachable_charges.add(matched[slot])
                changed = True
    neighbors = set().union(*(families[index] for index in reachable_charges))
    if not len(neighbors) < len(reachable_charges):
        raise AssertionError("exclusive-choice Hall witness is not deficient")
    return (
        charges,
        len(matched),
        sorted(reachable_charges),
        sorted(neighbors),
    )


def tree_coloring(
    tree: Tree, colorings: base.DecomposableColorings
) -> tuple[int, int]:
    """Return the support mask and triple-color bits of one explicit tree."""
    if isinstance(tree, int):
        return 1 << tree, 0
    lower_mask, lower_bits = tree_coloring(tree[0], colorings)
    upper_mask, upper_bits = tree_coloring(tree[1], colorings)
    support = lower_mask | upper_mask
    bits = (
        lower_bits
        | upper_bits
        | colorings.crossing_bits(support, lower_mask)
    )
    return support, bits


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def produce(repo: Path) -> dict[str, object]:
    maximum_n = 10
    strong_size = 7
    colorings = base.DecomposableColorings(maximum_n)
    support, bits = tree_coloring(ROOT_TREE, colorings)
    lower, lower_bits = tree_coloring(LOWER_TREE, colorings)
    upper, upper_bits = tree_coloring(UPPER_TREE, colorings)
    if support != (1 << maximum_n) - 1 or lower != 0x155 or upper != 0x2AA:
        raise AssertionError("explicit tree supports changed")
    if bits != EXPECTED_BITS:
        raise AssertionError("explicit tree coloring changed")
    if bits != lower_bits | upper_bits | colorings.crossing_bits(support, lower):
        raise AssertionError("root decomposition does not reconstruct coloring")

    analyzer = base.LocalSpanAnalysis(maximum_n, strong_size)
    local = analyzer.analyze(bits, support)
    if local is None:
        raise AssertionError("certificate unexpectedly contains a strong seven-set")
    groups, promotions = promotion.promoted_groups(
        local, support, lower, maximum_n
    )
    cap_rank_three = next(
        spans for color, rank, spans in groups if color == 0 and rank == 3
    )
    if cap_rank_three != EXPECTED_SPANS:
        raise AssertionError("adjusted cap/rank-three group changed")
    capacity = 10
    if len(cap_rank_three) <= capacity:
        raise AssertionError("certificate no longer violates capacity")
    adjusted_groups = [
        {
            "color": "cup" if color else "cap",
            "rank": rank,
            "spans": [list(span) for span in spans],
            "cardinality": len(spans),
        }
        for color, rank, spans in groups
    ]
    total_adjusted = sum(group["cardinality"] for group in adjusted_groups)
    untagged_pascal_window = sum(
        math.comb(strong_size - 2, rank - 1)
        for rank in range(2, strong_size)
    )
    if total_adjusted <= untagged_pascal_window:
        raise AssertionError("two-color all-rank aggregate no longer overflows")
    charges, matching_size, hall_demands, hall_neighbors = exclusive_choice_graph(
        local, support, lower, strong_size, groups, promotions
    )
    if len(charges) != 27 or matching_size != 20:
        raise AssertionError("exclusive-choice obstruction changed")

    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_adjusted_promotion_counterexample_k7_n10.py"
    return {
        "schema_version": 1,
        "experiment": "adjusted-promotion-capacity-counterexample-k7-n10",
        "generation_base_revision": base.git_revision(repo),
        "contract": {
            "domain": (
                "the explicit recursively decomposable alternating ten-point "
                "root encoded by the two recorded reverse-comb children"
            ),
            "success": (
                "an open context whose adjusted cap/rank-three demand has "
                "cardinality greater than choose(5,2)"
            ),
            "claim_boundary": (
                "counterexample certificate only; it refutes the proposed "
                "fixed-rank capacity and hence its adjusted Hall premise"
            ),
            "resource_limit": "30 minutes, 8 CPU cores, 16 GiB RAM, 5 GiB output",
        },
        "certificate": {
            "maximum_n": maximum_n,
            "strong_size": strong_size,
            "support_mask_hex": f"{support:x}",
            "lower_mask_hex": f"{lower:x}",
            "upper_mask_hex": f"{upper:x}",
            "coloring_hex": f"{bits:x}",
            "lower_tree": LOWER_TREE,
            "upper_tree": UPPER_TREE,
            "open": True,
            "color": "cap",
            "rank": 3,
            "adjusted_spans": [list(span) for span in cap_rank_three],
            "crossing_spans": [
                list(span)
                for span in cap_rank_three
                if bool(lower & (1 << span[0]))
                != bool(lower & (1 << span[1]))
            ],
            "promoted_spans": [
                list(span)
                for span in cap_rank_three
                if bool(lower & (1 << span[0]))
                == bool(lower & (1 << span[1]))
            ],
            "adjusted_cardinality": len(cap_rank_three),
            "pascal_capacity": capacity,
            "capacity_holds": False,
            "promotions": list(promotions),
            "adjusted_groups": adjusted_groups,
            "total_adjusted_cardinality": total_adjusted,
            "untagged_pascal_window": untagged_pascal_window,
            "untagged_aggregate_capacity_holds": False,
            "exclusive_choice_gate": {
                "charges": charges,
                "charge_count": len(charges),
                "maximum_matching_cardinality": matching_size,
                "matching_exists": False,
                "hall_witness_demand_indices": hall_demands,
                "hall_witness_demand_cardinality": len(hall_demands),
                "hall_witness_neighbor_slot_mask_hex": slot_family_mask(
                    set(hall_neighbors)
                ),
                "hall_witness_neighbor_cardinality": len(hall_neighbors),
            },
        },
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": base.file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": base.file_sha256(checker),
            },
            "producer_rank_base": {
                "path": "scripts/enumerate_allocated_span_pascal_demand.py",
                "sha256": base.file_sha256(
                    repo / "scripts/enumerate_allocated_span_pascal_demand.py"
                ),
            },
            "independent_rank_base": {
                "path": "scripts/check_allocated_span_pascal_demand.py",
                "sha256": base.file_sha256(
                    repo / "scripts/check_allocated_span_pascal_demand.py"
                ),
            },
            "direct_promotion_base": {
                "path": "scripts/check_rank_two_gap_promotion_k7.py",
                "sha256": base.file_sha256(
                    repo / "scripts/check_rank_two_gap_promotion_k7.py"
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
