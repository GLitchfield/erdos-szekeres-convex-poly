#!/usr/bin/env python3
"""Independently replay the bounded singleton-root rank experiment.

This checker imports no producer code.  It regenerates the complete coloring
set, recomputes every open parent and rank state, validates the explicit
collision trees, and proves the reported clique number by solving vertex cover
on the complement compatibility graph.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def line_digest(lines) -> str:
    value = hashlib.sha256()
    for line in lines:
        value.update(line.encode("ascii"))
        value.update(b"\n")
    return value.hexdigest()


def freeze(value):
    if isinstance(value, list):
        return tuple(freeze(item) for item in value)
    return value


def triples_for(n: int):
    triples = tuple(itertools.combinations(range(n), 3))
    return triples, {triple: i for i, triple in enumerate(triples)}


def split_coloring(mask: int, lower: int, triples, positions) -> int:
    value = 0
    for triple in triples:
        triple_mask = sum(1 << vertex for vertex in triple)
        if triple_mask & mask != triple_mask:
            continue
        memberships = tuple(bool(lower & (1 << vertex)) for vertex in triple)
        if 0 < sum(memberships) < 3 and memberships[1]:
            value |= 1 << positions[triple]
    return value


def submasks(mask: int):
    value = (mask - 1) & mask
    while value:
        yield value
        value = (value - 1) & mask


def generate_colorings(target: int, triples, positions) -> set[int]:
    table: dict[int, set[int]] = {}
    target_size = target.bit_count()
    for size in range(1, target_size + 1):
        for vertices in itertools.combinations(
                [v for v in range(target.bit_length()) if target & (1 << v)], size):
            mask = sum(1 << vertex for vertex in vertices)
            if size == 1:
                table[mask] = {0}
                continue
            values: set[int] = set()
            for lower in submasks(mask):
                upper = mask ^ lower
                crossing = split_coloring(mask, lower, triples, positions)
                for left in table[lower]:
                    for right in table[upper]:
                        values.add(left | right | crossing)
            table[mask] = values
    return table[target]


def bit(bits: int, positions, a: int, b: int, c: int) -> bool:
    return bool(bits & (1 << positions[(a, b, c)]))


def has_strong(bits: int, n: int, k: int, positions) -> bool:
    for subset in itertools.combinations(range(n), k):
        valid = True
        for a, b, c, d in itertools.combinations(subset, 4):
            if bit(bits, positions, a, b, c) != bit(bits, positions, a, b, d):
                valid = False
                break
            if bit(bits, positions, a, c, d) != bit(bits, positions, b, c, d):
                valid = False
                break
        if valid:
            return True
    return False


def states(bits: int, vertices: tuple[int, ...], clip: int, positions):
    pair_values: dict[tuple[int, int], tuple[int, int]] = {}
    words: list[int] = []
    for right_position, right in enumerate(vertices):
        rectangles: set[tuple[int, int]] = set()
        for left_position, left in enumerate(vertices[:right_position]):
            false_rank = true_rank = 1
            for predecessor in vertices[:left_position]:
                old_false, old_true = pair_values[(predecessor, left)]
                if bit(bits, positions, predecessor, left, right):
                    true_rank = min(clip, max(true_rank, old_true + 1))
                else:
                    false_rank = min(clip, max(false_rank, old_false + 1))
            pair_values[(left, right)] = false_rank, true_rank
            rectangles |= set(itertools.product(
                range(1, false_rank + 1), range(1, true_rank + 1)))
        word = sum(1 << (clip * (a - 1) + b - 1) for a, b in rectangles)
        words.append(word)
    matrix = tuple(pair_values[pair] for pair in itertools.combinations(vertices, 2))
    return tuple(words), matrix


def parse_tree(value):
    if isinstance(value, int):
        return value
    if not isinstance(value, dict) or set(value) != {"lower", "upper"}:
        raise ValueError("invalid decomposition tree")
    return parse_tree(value["lower"]), parse_tree(value["upper"])


def leaf_set(tree) -> frozenset[int]:
    if isinstance(tree, int):
        return frozenset((tree,))
    left = leaf_set(tree[0])
    right = leaf_set(tree[1])
    if left & right:
        raise ValueError("overlapping tree children")
    return left | right


def tree_turn(tree, triple: tuple[int, int, int]) -> bool:
    if isinstance(tree, int):
        raise ValueError("triple descended to leaf")
    left = leaf_set(tree[0])
    memberships = tuple(vertex in left for vertex in triple)
    if all(memberships):
        return tree_turn(tree[0], triple)
    if not any(memberships):
        return tree_turn(tree[1], triple)
    return memberships[1]


def tree_bits(tree, triples, positions) -> int:
    leaves = leaf_set(tree)
    return sum(
        1 << positions[triple]
        for triple in triples
        if set(triple) <= leaves and tree_turn(tree, triple)
    )


def minimum_vertex_cover_size(vertices: list[int], graph_edges: set[tuple[int, int]]) -> int:
    """Exact branching checker; the graph here is the sparse complement."""
    ordered_edges = tuple(sorted(graph_edges))

    def possible(edges: tuple[tuple[int, int], ...], budget: int) -> bool:
        if not edges:
            return True
        if budget == 0:
            return False
        a, b = edges[0]
        without_a = tuple(edge for edge in edges if a not in edge)
        if possible(without_a, budget - 1):
            return True
        without_b = tuple(edge for edge in edges if b not in edge)
        return possible(without_b, budget - 1)

    for size in range(len(vertices) + 1):
        if possible(ordered_edges, size):
            return size
    raise AssertionError("finite graph had no vertex cover")


def validate_collision(entry, state_kind: str, upper_vertices, n, clip,
                       triples, positions) -> dict[str, bool]:
    equal_child = freeze(entry["equal_child_state"])
    outputs = []
    checks: dict[str, bool] = {}
    for side in ("left", "right"):
        witness = entry[side]
        upper_tree = parse_tree(witness["upper_tree"])
        parent_tree = (1, upper_tree)
        upper_bits = int(witness["upper_coloring_hex"], 16)
        parent_bits = int(witness["parent_coloring_hex"], 16)
        child = states(upper_bits, upper_vertices, clip, positions)
        parent = states(parent_bits, tuple(range(n)), clip, positions)
        state_index = 0 if state_kind == "word" else 1
        outputs.append(parent[state_index])
        checks[f"{side}_upper_tree_leaves"] = leaf_set(upper_tree) == frozenset(upper_vertices)
        checks[f"{side}_upper_tree_coloring"] = tree_bits(upper_tree, triples, positions) == upper_bits
        checks[f"{side}_parent_tree_coloring"] = tree_bits(parent_tree, triples, positions) == parent_bits
        checks[f"{side}_child_state"] = child[state_index] == equal_child
        checks[f"{side}_parent_state"] = parent[state_index] == freeze(witness["parent_state"])
        checks[f"{side}_open"] = not has_strong(parent_bits, n, 6, positions)
    checks["equal_child_states"] = True
    checks["unequal_parent_states"] = outputs[0] != outputs[1]
    difference = entry["first_difference"]
    index = difference["index"]
    checks["first_difference"] = (
        outputs[0][:index] == outputs[1][:index]
        and outputs[0][index] == freeze(difference["left"])
        and outputs[1][index] == freeze(difference["right"])
        and outputs[0][index] != outputs[1][index]
    )
    return checks


def replay(certificate: dict[str, object]) -> dict[str, object]:
    if certificate.get("schema_version") != 1:
        raise ValueError("unsupported schema")
    producer = Path(__file__).resolve().parent / "analyze_decomposable_rank_profiles.py"
    scope = certificate["scope"]
    n, k, clip = scope["n"], scope["k"], scope["rank_clip"]
    if (n, k, clip) != (9, 6, 4):
        raise ValueError("checker is intentionally specialized to n=9, k=6")
    lower = int(scope["lower_mask_hex"], 16)
    upper = int(scope["upper_mask_hex"], 16)
    triples, positions = triples_for(n)
    width = (len(triples) + 3) // 4
    upper_vertices = tuple(v for v in range(n) if upper & (1 << v))
    colorings = generate_colorings(upper, triples, positions)
    fixed = split_coloring((1 << n) - 1, lower, triples, positions)

    word_seen = {}
    matrix_seen = {}
    word_collision_count = matrix_collision_count = injectivity_count = 0
    open_count = 0
    universe: set[int] = set()
    compatibility: set[tuple[int, int]] = set()
    rows: list[str] = []
    for upper_bits in sorted(colorings):
        parent_bits = upper_bits | fixed
        if has_strong(parent_bits, n, k, positions):
            continue
        open_count += 1
        child_word, child_matrix = states(upper_bits, upper_vertices, clip, positions)
        parent_word, parent_matrix = states(parent_bits, tuple(range(n)), clip, positions)
        rows.append(
            f"{upper_bits:0{width}x}:"
            f"{','.join(map(str, child_word))}:"
            f"{','.join(map(str, parent_word))}"
        )
        injectivity_count += len(parent_word) != len(set(parent_word))
        present = sorted(set(parent_word))
        universe.update(present)
        compatibility.update(itertools.combinations(present, 2))
        if child_word in word_seen:
            word_collision_count += word_seen[child_word] != parent_word
        else:
            word_seen[child_word] = parent_word
        if child_matrix in matrix_seen:
            matrix_collision_count += matrix_seen[child_matrix] != parent_matrix
        else:
            matrix_seen[child_matrix] = parent_matrix

    summary = certificate["search_summary"]
    checks = {
        "producer_identity": certificate["producer"] ==
            "scripts/analyze_decomposable_rank_profiles.py",
        "producer_sha256": certificate["producer_sha256"] ==
            hashlib.sha256(producer.read_bytes()).hexdigest(),
        "root_partition": lower == 2 and lower | upper == (1 << n) - 1 and not lower & upper,
        "crossing_bits": int(scope["crossing_bits_hex"], 16) == fixed,
        "upper_coloring_count": summary["upper_coloring_count"] == len(colorings),
        "upper_colorings_sha256": summary["upper_colorings_sha256"] == line_digest(
            f"{bits:0{width}x}" for bits in sorted(colorings)),
        "open_parent_count": summary["open_parent_count"] == open_count,
        "open_rank_rows_sha256": summary["open_rank_rows_sha256"] == line_digest(rows),
        "distinct_child_downset_words": summary["distinct_child_downset_words"] == len(word_seen),
        "downset_word_collision_observations":
            summary["downset_word_collision_observations"] == word_collision_count,
        "distinct_child_pair_rank_matrices":
            summary["distinct_child_pair_rank_matrices"] == len(matrix_seen),
        "pair_rank_matrix_collision_observations":
            summary["pair_rank_matrix_collision_observations"] == matrix_collision_count,
        "parent_vertex_downset_injectivity_violations":
            summary["parent_vertex_downset_injectivity_violations"] == injectivity_count,
    }
    checks.update({
        f"downset_collision_{name}": value for name, value in validate_collision(
            certificate["downset_collision"], "word", upper_vertices, n, clip,
            triples, positions).items()
    })
    checks.update({
        f"pair_rank_collision_{name}": value for name, value in validate_collision(
            certificate["pair_rank_collision"], "matrix", upper_vertices, n, clip,
            triples, positions).items()
    })

    graph = certificate["parent_downset_compatibility"]
    all_pairs = set(itertools.combinations(sorted(universe), 2))
    complement = all_pairs - compatibility
    clique = tuple(graph["maximum_clique"])
    clique_edges = set(itertools.combinations(clique, 2))
    cover_size = minimum_vertex_cover_size(sorted(universe), complement)
    checks.update({
        "downset_vertices": graph["vertices"] == sorted(universe),
        "downset_vertex_count": graph["vertex_count"] == len(universe),
        "compatibility_edge_count": graph["edge_count"] == len(compatibility),
        "compatibility_edges_sha256": graph["edges_sha256"] == line_digest(
            f"{a},{b}" for a, b in sorted(compatibility)),
        "reported_clique_is_clique": len(set(clique)) == len(clique)
            and set(clique) <= universe and clique_edges <= compatibility,
        "maximum_clique_size": graph["maximum_clique_size"] == len(universe) - cover_size,
        "reported_clique_is_maximum": len(clique) == len(universe) - cover_size,
    })
    return {"checks": checks, "ok": all(checks.values())}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    result = replay(json.loads(args.certificate.read_text()))
    result["certificate"] = str(args.certificate)
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
