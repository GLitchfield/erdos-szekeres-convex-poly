#!/usr/bin/env python3
"""Produce the frozen stable-ownership one-hole descent gate.

The rule is deliberately local and deterministic.  Ideals are ordered by
their row-boundary tuple, lexicographically from the empty boundary upward.
If a hole is not directly fillable, it takes its least-priority candidate and
passes the hole to that candidate's unique current owner.  This preserves
candidate membership and injectivity without consulting a completed matching.
"""

from __future__ import annotations

import argparse
import itertools
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


State = tuple[int, ...]


def ideal_boundary(mask: int, rows: int, columns: int) -> tuple[int, ...]:
    """Return the row-length boundary of a rectangular lower ideal."""
    heights = tuple(
        sum(bool(mask & (1 << (row * columns + column)))
            for column in range(columns))
        for row in range(rows)
    )
    if any(heights[index] < heights[index + 1]
           for index in range(len(heights) - 1)):
        raise AssertionError("mask is not a rectangular lower ideal")
    for row, height in enumerate(heights):
        expected = sum(1 << (row * columns + column)
                       for column in range(height))
        actual = mask & (((1 << columns) - 1) << (row * columns))
        if actual != expected:
            raise AssertionError("ideal row is not a prefix")
    return heights


def candidate_priority(mask: int, rows: int, columns: int) -> tuple[object, ...]:
    """The frozen boundary-only priority, with mask as a deterministic tie-break."""
    return ideal_boundary(mask, rows, columns) + (mask,)


def enumerate_hole_states(
    candidates: tuple[tuple[int, ...], ...],
) -> tuple[State, ...]:
    """Enumerate every injective representative assignment with one hole."""
    states = []
    for hole in range(len(candidates)):
        represented = tuple(index for index in range(len(candidates))
                            if index != hole)
        for choices in itertools.product(*(candidates[index]
                                           for index in represented)):
            if len(set(choices)) != len(choices):
                continue
            state = [-1] * len(candidates)
            for index, ideal in zip(represented, choices, strict=True):
                state[index] = ideal
            states.append(tuple(state))
    return tuple(states)


def successor(
    state: State,
    candidates: tuple[tuple[int, ...], ...],
    rows: int,
    columns: int,
) -> State | None:
    """Return the ownership-transfer successor, or `None` when fillable."""
    hole = state.index(-1)
    owner = {ideal: index for index, ideal in enumerate(state) if ideal != -1}
    ordered = sorted(candidates[hole],
                     key=lambda ideal: candidate_priority(ideal, rows, columns))
    if any(ideal not in owner for ideal in ordered):
        return None
    selected = ordered[0]
    previous_owner = owner[selected]
    answer = list(state)
    answer[hole] = selected
    answer[previous_owner] = -1
    return tuple(answer)


def canonical_cycle(cycle: tuple[State, ...]) -> tuple[State, ...]:
    rotations = tuple(cycle[offset:] + cycle[:offset]
                      for offset in range(len(cycle)))
    return min(rotations)


def state_record(state: State) -> dict[str, object]:
    return {
        "hole_index": state.index(-1),
        "representatives_hex": [None if ideal == -1 else f"{ideal:x}"
                                for ideal in state],
    }


def analyze_functional_graph(
    states: tuple[State, ...],
    candidates: tuple[tuple[int, ...], ...],
    rows: int,
    columns: int,
) -> dict[str, object]:
    state_set = set(states)
    successors: dict[State, State | None] = {}
    fillable = 0
    for state in states:
        next_state = successor(state, candidates, rows, columns)
        if next_state is None:
            fillable += 1
        elif next_state not in state_set:
            raise AssertionError("ownership transfer left the one-hole state space")
        successors[state] = next_state

    unfillable_states = tuple(
        state for state in states if successors[state] is not None
    )
    one_transfer_fillable = sum(
        successors[successors[state]] is None
        for state in unfillable_states
    )
    initial_unfillable_holes = sorted(
        {state.index(-1) for state in unfillable_states}
    )
    post_transfer_holes = sorted(
        {successors[state].index(-1) for state in unfillable_states}
    )

    outcomes: dict[State, tuple[str, tuple[State, ...] | None]] = {}
    cycles: set[tuple[State, ...]] = set()
    for start in states:
        if start in outcomes:
            continue
        path: list[State] = []
        position: dict[State, int] = {}
        current: State | None = start
        while current is not None and current not in outcomes and current not in position:
            position[current] = len(path)
            path.append(current)
            current = successors[current]
        if current is None:
            outcome: tuple[str, tuple[State, ...] | None] = ("fillable", None)
        elif current in outcomes:
            outcome = outcomes[current]
        else:
            cycle = canonical_cycle(tuple(path[position[current]:]))
            cycles.add(cycle)
            outcome = ("cycle", cycle)
        for state in reversed(path):
            outcomes[state] = outcome

    cycle_states = sum(outcome[0] == "cycle" for outcome in outcomes.values())
    first_cycle = min(cycles) if cycles else None
    return {
        "state_count": len(states),
        "directly_fillable_state_count": fillable,
        "unfillable_state_count": len(states) - fillable,
        "initial_unfillable_hole_indices": initial_unfillable_holes,
        "post_transfer_hole_indices": post_transfer_holes,
        "unfillable_states_fillable_after_one_transfer": one_transfer_fillable,
        "all_unfillable_fill_after_one_transfer": (
            one_transfer_fillable == len(unfillable_states)
        ),
        "all_successors_are_valid_states": True,
        "states_reaching_fillable": len(states) - cycle_states,
        "states_reaching_cycle": cycle_states,
        "directed_cycle_count": len(cycles),
        "all_states_reach_fillable": cycle_states == 0,
        "first_cycle": None if first_cycle is None else {
            "length": len(first_cycle),
            "states": [state_record(state) for state in first_cycle],
        },
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
    vertices = tuple(vertex for vertex in range(maximum_n)
                     if support & (1 << vertex))
    selected = None
    for color, rank, frontier in context_groups(
        local, support, lower, maximum_n
    ):
        if color == 0 and rank == 3:
            original, _, _, _ = endpoint_transition_candidates(
                local, vertices, frontier, color, rank, strong_size
            )
            candidates = oriented_candidates(
                original, frontier, lower, rank - 1,
                strong_size - rank - 1
            )
            selected = (rank, frontier, candidates)
            break
    if selected is None:
        raise AssertionError("frozen cap/rank-three frontier is absent")
    rank, frontier, candidates = selected
    rows = rank - 1
    columns = strong_size - rank - 1
    states = enumerate_hole_states(candidates)
    counts_by_hole = [sum(state[hole] == -1 for state in states)
                      for hole in range(len(candidates))]
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "color": "cap",
        "rank": rank,
        "rows": rows,
        "columns": columns,
        "frontier": [list(span) for span in frontier],
        "candidate_families_hex": [
            [f"{ideal:x}" for ideal in family] for family in candidates
        ],
        "state_counts_by_hole": counts_by_hole,
        "functional_graph": analyze_functional_graph(
            states, candidates, rows, columns
        ),
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_stable_ownership_hole_descent.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-stable-ownership-hole-descent-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "state": (
                "one hole and injective untagged representatives for every "
                "other cap/rank-three frontier span"
            ),
            "priority": (
                "candidate row-boundary tuples in ascending lexicographic "
                "order, with the ideal cell mask as deterministic tie-break"
            ),
            "move": (
                "an unfillable hole takes its first candidate and transfers "
                "the hole to that ideal's unique current owner"
            ),
            "claim_boundary": (
                "bounded deterministic functional-graph gate only; no general "
                "termination, Hall, or geometric conclusion"
            ),
        },
        "frozen_n12_k7_cap_rank3": frozen_record(),
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
