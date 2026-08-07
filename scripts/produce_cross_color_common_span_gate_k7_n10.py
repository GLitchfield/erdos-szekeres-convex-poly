#!/usr/bin/env python3
"""Produce the bounded common-span cross-color reuse gate at k=7, n=10.

The finite endpoint-candidate graph is repaired by merging the seven cap/cup
rank-three charges with identical endpoints and intersecting their candidate
families.  The same certificate records why that combinatorial repair has no
published-induction semantics: the active rays live in disjoint children and
one Pascal coefficient is arithmetically insufficient for the two increments.
"""

from __future__ import annotations

import argparse
import json
import math
import os
from pathlib import Path

import enumerate_allocated_span_pascal_demand as base
import enumerate_rank_two_gap_promotion_k7 as promotion
import produce_adjusted_promotion_counterexample_k7_n10 as previous


def family_from_mask(mask: str) -> set[int]:
    value = int(mask, 16)
    return {slot for slot in range(32) if value & (1 << slot)}


def family_mask(family: set[int]) -> str:
    return f"{sum(1 << slot for slot in family):08x}"


def maximum_matching(families: list[set[int]]) -> tuple[int, list[list[int]]]:
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

    for charge in range(len(families)):
        augment(charge, set())
    assignment = sorted([[charge, slot] for slot, charge in matched.items()])
    return len(matched), assignment


def threshold(a: int, u: int, k: int) -> int:
    if a == 1 or u == 1:
        return 0
    if a + u <= k + 3:
        return math.comb(a + u - 4, a - 2)
    return sum(math.comb(k - 2, j) for j in range(k - a, u - 1))


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def produce(repo: Path) -> dict[str, object]:
    maximum_n = 10
    strong_size = 7
    colorings = base.DecomposableColorings(maximum_n)
    support, bits = previous.tree_coloring(previous.ROOT_TREE, colorings)
    lower, _ = previous.tree_coloring(previous.LOWER_TREE, colorings)
    upper, _ = previous.tree_coloring(previous.UPPER_TREE, colorings)
    local = base.LocalSpanAnalysis(maximum_n, strong_size).analyze(bits, support)
    if local is None:
        raise AssertionError("ten-point gate unexpectedly contains a strong seven-set")
    groups, promotions = promotion.promoted_groups(
        local, support, lower, maximum_n
    )
    crossing_by_color: dict[int, tuple[tuple[int, int], ...]] = {}
    for color in (0, 1):
        rank_three = next(
            spans for group_color, rank, spans in groups
            if group_color == color and rank == 3
        )
        crossing_by_color[color] = tuple(
            span for span in rank_three
            if bool(lower & (1 << span[0])) != bool(lower & (1 << span[1]))
        )
    common_spans = tuple(sorted(
        set(crossing_by_color[0]) & set(crossing_by_color[1])
    ))
    if common_spans != tuple((left, left + 3) for left in range(7)):
        raise AssertionError("common rank-three span family changed")

    original, _, _, _ = previous.exclusive_choice_graph(
        local, support, lower, strong_size, groups, promotions
    )
    common_records: dict[tuple[int, int], dict[str, dict[str, object]]] = {}
    retained: list[tuple[dict[str, object], set[int]]] = []
    for charge in original:
        family = family_from_mask(charge["candidate_slot_mask_hex"])
        if charge["kind"] == "higher-rank-crossing" and charge["rank"] == 3:
            span = tuple(charge["span"])
            common_records.setdefault(span, {})[charge["color"]] = charge
        else:
            retained.append((dict(charge), family))

    charges: list[dict[str, object]] = []
    families: list[set[int]] = []
    for charge, family in retained[:9]:
        charges.append(charge)
        families.append(family)
    for span in common_spans:
        records = common_records[span]
        cap_family = family_from_mask(records["cap"]["candidate_slot_mask_hex"])
        cup_family = family_from_mask(records["cup"]["candidate_slot_mask_hex"])
        shared_family = cap_family & cup_family
        left_in_lower = bool(lower & (1 << span[0]))
        charges.append({
            "kind": "cross-color-common-span",
            "rank": 3,
            "span": list(span),
            "cap_candidate_slot_mask_hex": family_mask(cap_family),
            "cup_candidate_slot_mask_hex": family_mask(cup_family),
            "candidate_slot_mask_hex": family_mask(shared_family),
            "cup_active_child": "lower",
            "cap_active_child": "upper",
            "cup_ray_direction": "right" if left_in_lower else "left",
            "cap_ray_direction": "left" if left_in_lower else "right",
        })
        families.append(shared_family)
    for charge, family in retained[9:]:
        charges.append(charge)
        families.append(family)

    matching_size, assignment = maximum_matching(families)
    if len(charges) != 20 or matching_size != 20:
        raise AssertionError("common-span quotient no longer has a perfect matching")

    successor_total = threshold(7, 4, 7) + threshold(4, 7, 7)
    demand = math.comb(5, 2)
    one_demand_total = threshold(7, 3, 7) + threshold(3, 7, 7) + demand
    if successor_total != 32 or one_demand_total != 22:
        raise AssertionError("bounded threshold arithmetic changed")

    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_cross_color_common_span_gate_k7_n10.py"
    return {
        "schema_version": 1,
        "experiment": "cross-color-common-span-gate-k7-n10",
        "generation_base_revision": base.git_revision(repo),
        "contract": {
            "domain": (
                "the explicit open alternating ten-point decomposable root, "
                "with only identical-endpoint cap/cup rank-three charges merged"
            ),
            "success": (
                "a perfect matching plus a sound one-coefficient semantic payoff"
            ),
            "outcome": (
                "the matching passes, but disjoint active children and 32 > 22 "
                "refute retained-subset and single-coefficient semantics"
            ),
            "claim_boundary": (
                "this retires common endpoints as a standalone proof-reuse rule; "
                "it does not refute stronger nonadditive geometric invariants"
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
            "open": True,
            "common_rank_three_spans": [list(span) for span in common_spans],
            "common_span_count": len(common_spans),
            "active_child_intersection_mask_hex": f"{lower & upper:x}",
            "quotient_charges": charges,
            "quotient_charge_count": len(charges),
            "maximum_matching_cardinality": matching_size,
            "perfect_matching": assignment,
            "published_arithmetic": {
                "successor_threshold_total": successor_total,
                "base_threshold_total": threshold(7, 3, 7) + threshold(3, 7, 7),
                "single_pascal_demand": demand,
                "single_demand_total": one_demand_total,
                "single_demand_suffices": False,
                "deficit": successor_total - one_demand_total,
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
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("data/derived/e3-cross-color-common-span-gate-k7-n10.json"),
    )
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    output = args.output if args.output.is_absolute() else repo / args.output
    write_atomic(output, produce(repo))
    print(output)


if __name__ == "__main__":
    main()
