#!/usr/bin/env python3
"""Independently replay the stable-ownership one-hole descent gate."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from check_allocated_span_pascal_demand import (
    Replay,
    file_sha256,
    groups,
    height_mask_hex,
    replay_transition_candidates,
)


Tree = int | tuple["Tree", "Tree"]
LOWER_TREE: Tree = ((8, (2, 1)), ((4, 7), 10))
UPPER_TREE: Tree = (((0, 3), ((6, 9), 5)), 11)
TREE: Tree = (LOWER_TREE, UPPER_TREE)
Ideal = tuple[int, ...]
State = tuple[Ideal | None, ...]


def vertices(tree: Tree) -> tuple[int, ...]:
    if isinstance(tree, int):
        return (tree,)
    return tuple(sorted(vertices(tree[0]) + vertices(tree[1])))


def coloring_bits(tree: Tree, machine: Replay) -> int:
    if isinstance(tree, int):
        return 0
    left, right = tree
    support = sum(1 << vertex for vertex in vertices(tree))
    lower = sum(1 << vertex for vertex in vertices(left))
    return coloring_bits(left, machine) | coloring_bits(right, machine) | machine.crossing(
        support, lower
    )


def reflected(ideal: Ideal, columns: int) -> Ideal:
    return tuple(columns - height for height in reversed(ideal))


def ideal_hex(ideal: Ideal, columns: int) -> str:
    return height_mask_hex(ideal, columns)


def enumerate_hole_states(
    candidates: tuple[tuple[Ideal, ...], ...],
) -> tuple[State, ...]:
    states = []
    for hole in range(len(candidates)):
        represented = tuple(index for index in range(len(candidates))
                            if index != hole)
        for choices in itertools.product(*(candidates[index]
                                           for index in represented)):
            if len(set(choices)) != len(choices):
                continue
            state: list[Ideal | None] = [None] * len(candidates)
            for index, ideal in zip(represented, choices, strict=True):
                state[index] = ideal
            states.append(tuple(state))
    return tuple(states)


def successor(state: State, candidates: tuple[tuple[Ideal, ...], ...]) -> State | None:
    hole = state.index(None)
    owner = {ideal: index for index, ideal in enumerate(state)
             if ideal is not None}
    ordered = sorted(candidates[hole])
    if any(ideal not in owner for ideal in ordered):
        return None
    selected = ordered[0]
    previous_owner = owner[selected]
    answer = list(state)
    answer[hole] = selected
    answer[previous_owner] = None
    return tuple(answer)


def state_key(state: State, columns: int) -> tuple[int, ...]:
    return tuple(-1 if ideal is None else int(ideal_hex(ideal, columns), 16)
                 for ideal in state)


def canonical_cycle(cycle: tuple[State, ...], columns: int) -> tuple[State, ...]:
    rotations = tuple(cycle[offset:] + cycle[:offset]
                      for offset in range(len(cycle)))
    return min(rotations, key=lambda states: tuple(state_key(state, columns)
                                                   for state in states))


def state_record(state: State, columns: int) -> dict[str, object]:
    return {
        "hole_index": state.index(None),
        "representatives_hex": [None if ideal is None else ideal_hex(ideal, columns)
                                for ideal in state],
    }


def analyze_functional_graph(
    states: tuple[State, ...],
    candidates: tuple[tuple[Ideal, ...], ...],
    columns: int,
) -> dict[str, object]:
    state_set = set(states)
    successors: dict[State, State | None] = {}
    fillable = 0
    for state in states:
        next_state = successor(state, candidates)
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
        {state.index(None) for state in unfillable_states}
    )
    post_transfer_holes = sorted(
        {successors[state].index(None) for state in unfillable_states}
    )

    outcomes: dict[State, tuple[str, tuple[State, ...] | None]] = {}
    cycles: dict[tuple[tuple[int, ...], ...], tuple[State, ...]] = {}
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
            cycle = canonical_cycle(tuple(path[position[current]:]), columns)
            key = tuple(state_key(state, columns) for state in cycle)
            cycles[key] = cycle
            outcome = ("cycle", cycle)
        for state in reversed(path):
            outcomes[state] = outcome

    cycle_states = sum(outcome[0] == "cycle" for outcome in outcomes.values())
    first_cycle = cycles[min(cycles)] if cycles else None
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
            "states": [state_record(state, columns) for state in first_cycle],
        },
    }


def frozen_record() -> dict[str, object]:
    maximum_n = 12
    strong_size = 7
    machine = Replay(maximum_n, strong_size)
    support_vertices = vertices(TREE)
    support = sum(1 << vertex for vertex in support_vertices)
    lower = sum(1 << vertex for vertex in vertices(LOWER_TREE))
    bits = coloring_bits(TREE, machine)
    local = machine.ranks(bits, support)
    if local is None:
        raise AssertionError("frozen root unexpectedly contains a strong seven")
    selected = None
    for color, rank, frontier in groups(local, support, lower, maximum_n):
        if color == 0 and rank == 3:
            original, _, _, _ = replay_transition_candidates(
                local, support_vertices, frontier, color, rank, strong_size
            )
            columns = strong_size - rank - 1
            candidates = []
            for span, family in zip(frontier, original, strict=True):
                if lower & (1 << span[0]):
                    oriented = family
                else:
                    oriented = tuple(sorted(reflected(ideal, columns)
                                            for ideal in family))
                candidates.append(oriented)
            selected = (rank, frontier, tuple(candidates))
            break
    if selected is None:
        raise AssertionError("frozen cap/rank-three frontier is absent")
    rank, frontier, candidates = selected
    rows = rank - 1
    columns = strong_size - rank - 1
    states = enumerate_hole_states(candidates)
    counts_by_hole = [sum(state[hole] is None for state in states)
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
            sorted(
                (ideal_hex(ideal, columns) for ideal in family),
                key=lambda encoded: int(encoded, 16),
            )
            for family in candidates
        ],
        "state_counts_by_hole": counts_by_hole,
        "functional_graph": analyze_functional_graph(
            states, candidates, columns
        ),
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
    if replay != manifest["frozen_n12_k7_cap_rank3"]:
        raise AssertionError("independent stable-ownership replay differs")
    graph = replay["functional_graph"]
    print(
        "states=", graph["state_count"],
        "fillable=", graph["directly_fillable_state_count"],
        "cycles=", graph["directed_cycle_count"],
        "all_reach_fillable=", graph["all_states_reach_fillable"],
    )


if __name__ == "__main__":
    main()
