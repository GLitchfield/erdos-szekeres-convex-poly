#!/usr/bin/env python3
"""Enumerate the complete labeled local OneChange hierarchy through six.

The objects in this file are abstract ordered triple colorings (rank-three
signotopes), not point configurations and not sweep-realizability witnesses.
Every catalog is labeled and unquotiented.  Bit 1 means ``Turn.left`` and the
bit positions are lexicographically ordered triples, least-significant first.
"""

from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time


SCHEMA_VERSION = 1
MODEL = "complete labeled abstract OneChangeOn triple colorings"


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def pairs(n: int) -> tuple[tuple[int, int], ...]:
    return tuple(itertools.combinations(range(n), 2))


def one_change(values: tuple[bool, ...]) -> bool:
    return sum(left != right for left, right in zip(values, values[1:])) <= 1


def sha256_lines(lines: list[str]) -> str:
    return hashlib.sha256("".join(f"{line}\n" for line in lines).encode()).hexdigest()


def canonical_sha256(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def width(n: int) -> int:
    return max(1, (len(triples(n)) + 3) // 4)


def hex_mask(mask: int, n: int) -> str:
    return f"{mask:0{width(n)}x}"


def bit(mask: int, position: int) -> bool:
    return bool(mask & (1 << position))


def extend_parent(parent: int, old_n: int, pair_mask: int) -> int | None:
    """Return the new coloring, or ``None`` when a new quadruple forbids it."""
    old_triples = triples(old_n)
    old_position = {triple: index for index, triple in enumerate(old_triples)}
    pair_list = pairs(old_n)
    pair_position = {pair: index for index, pair in enumerate(pair_list)}
    for a, b, c in old_triples:
        values = (
            bit(parent, old_position[a, b, c]),
            bit(pair_mask, pair_position[a, b]),
            bit(pair_mask, pair_position[a, c]),
            bit(pair_mask, pair_position[b, c]),
        )
        if not one_change(values):
            return None

    new_vertex = old_n
    colors: dict[tuple[int, int, int], bool] = {
        triple: bit(parent, position) for position, triple in enumerate(old_triples)
    }
    colors.update({
        (a, b, new_vertex): bit(pair_mask, pair_position[a, b])
        for a, b in pair_list
    })
    return sum(
        int(colors[triple]) << position
        for position, triple in enumerate(triples(old_n + 1))
    )


def enumerate_hierarchy(max_n: int) -> tuple[dict[int, tuple[int, ...]],
                                              dict[int, tuple[tuple[int, int, int], ...]]]:
    """Build states by exact rightmost extension from the two three-point states."""
    levels: dict[int, tuple[int, ...]] = {3: (0, 1)}
    edges: dict[int, tuple[tuple[int, int, int], ...]] = {}
    for new_n in range(4, max_n + 1):
        old_n = new_n - 1
        rows: list[tuple[int, int, int]] = []
        children: set[int] = set()
        for parent in levels[old_n]:
            for pair_mask in range(1 << len(pairs(old_n))):
                child = extend_parent(parent, old_n, pair_mask)
                if child is None:
                    continue
                if child in children:
                    raise AssertionError("rightmost restriction was not unique")
                children.add(child)
                rows.append((parent, child, pair_mask))
        levels[new_n] = tuple(sorted(children))
        edges[new_n] = tuple(sorted(rows, key=lambda row: (row[1], row[0], row[2])))
    return levels, edges


def color(mask: int, position: dict[tuple[int, int, int], int],
          triple: tuple[int, int, int]) -> bool:
    return bit(mask, position[triple])


def is_monochromatic(mask: int, position: dict[tuple[int, int, int], int],
                     vertices: tuple[int, ...], expected: bool) -> bool:
    return all(color(mask, position, triple) == expected
               for triple in itertools.combinations(vertices, 3))


def is_strong(mask: int, position: dict[tuple[int, int, int], int],
              vertices: tuple[int, ...]) -> bool:
    for a, b, c, d in itertools.combinations(vertices, 4):
        if color(mask, position, (a, b, c)) != color(mask, position, (a, b, d)):
            return False
        if color(mask, position, (a, c, d)) != color(mask, position, (b, c, d)):
            return False
    return True


def maximum_subset(n: int, predicate) -> int:
    for size in range(n, 0, -1):
        if any(predicate(vertices)
               for vertices in itertools.combinations(range(n), size)):
            return size
    raise AssertionError("a singleton subset always satisfies the local predicates")


def recursively_decomposable(mask: int, n: int) -> bool:
    """Test recursive directed deep-below splitting on the full labeled support."""
    triple_list = triples(n)
    position = {triple: index for index, triple in enumerate(triple_list)}

    @lru_cache(maxsize=None)
    def decomposes(support: int) -> bool:
        if support.bit_count() <= 1:
            return True
        lower = (support - 1) & support
        while lower:
            if lower != support:
                upper = support ^ lower
                compatible = True
                for triple in triple_list:
                    triple_support = sum(1 << vertex for vertex in triple)
                    if triple_support & support != triple_support:
                        continue
                    wholly_lower = triple_support & lower == triple_support
                    wholly_upper = triple_support & upper == triple_support
                    if wholly_lower or wholly_upper:
                        continue
                    required = bool(lower & (1 << triple[1]))
                    if color(mask, position, triple) != required:
                        compatible = False
                        break
                if compatible and decomposes(lower) and decomposes(upper):
                    return True
            lower = (lower - 1) & support
        return False

    return decomposes((1 << n) - 1)


def state_annotations(mask: int, n: int) -> dict[str, object]:
    position = {triple: index for index, triple in enumerate(triples(n))}
    cup = maximum_subset(
        n, lambda vertices: is_monochromatic(mask, position, vertices, True))
    cap = maximum_subset(
        n, lambda vertices: is_monochromatic(mask, position, vertices, False))
    strong = maximum_subset(
        n, lambda vertices: is_strong(mask, position, vertices))
    return {
        "cap_maximum": cap,
        "cup_maximum": cup,
        "decomposable": recursively_decomposable(mask, n),
        "strong_maximum": strong,
    }


def reflect_color(mask: int, n: int) -> int:
    return mask ^ ((1 << len(triples(n))) - 1)


def reverse_order(mask: int, n: int) -> int:
    """Reverse labels and flip each oriented triple's color."""
    position = {triple: index for index, triple in enumerate(triples(n))}
    result = 0
    for new_position, (a, b, c) in enumerate(triples(n)):
        old_triple = (n - 1 - c, n - 1 - b, n - 1 - a)
        old_color = bit(mask, position[old_triple])
        result |= int(not old_color) << new_position
    return result


def symmetry_rows(states: tuple[int, ...], n: int, transform) -> list[str]:
    return [f"{hex_mask(state, n)}>{hex_mask(transform(state, n), n)}"
            for state in states]


def pair_principal_spectrum(mask: int, n: int) -> tuple[tuple[int, int, int], ...]:
    """Compute the frozen ``pair-principal-spectrum-v1`` summary."""
    pair_list = pairs(n)
    pair_position = {pair: index for index, pair in enumerate(pair_list)}
    triple_position = {triple: index for index, triple in enumerate(triples(n))}
    reach = [1 << index for index in range(len(pair_list))]
    for i, j, k in triples(n):
        ij = pair_position[i, j]
        ik = pair_position[i, k]
        jk = pair_position[j, k]
        if bit(mask, triple_position[i, j, k]):
            reach[jk] |= 1 << ik
            reach[ik] |= 1 << ij
        else:
            reach[ij] |= 1 << ik
            reach[ik] |= 1 << jk
    for middle in range(len(pair_list)):
        middle_bit = 1 << middle
        for source in range(len(pair_list)):
            if reach[source] & middle_bit:
                reach[source] |= reach[middle]

    raw = []
    for pair_index in range(len(pair_list)):
        strongly_connected = sum(
            bool(reach[pair_index] & (1 << other)
                 and reach[other] & (1 << pair_index))
            for other in range(len(pair_list))
        )
        lower = sum(bool(reach[other] & (1 << pair_index))
                    for other in range(len(pair_list)))
        upper = reach[pair_index].bit_count()
        raw.append((strongly_connected, lower, upper))
    raw_profile = tuple(sorted(raw))
    dual_profile = tuple(sorted((scc, upper, lower)
                                for scc, lower, upper in raw_profile))
    return min(raw_profile, dual_profile)


def symmetry_orbit(mask: int, n: int) -> frozenset[int]:
    pending = [mask]
    orbit: set[int] = set()
    while pending:
        current = pending.pop()
        if current in orbit:
            continue
        orbit.add(current)
        pending.append(reflect_color(current, n))
        pending.append(reverse_order(current, n))
    return frozenset(orbit)


def validate_frozen_summary(path: Path, expected_sha256: str) -> dict[str, object]:
    actual_sha256 = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual_sha256 != expected_sha256:
        raise ValueError("frozen summary SHA-256 does not match the admitted digest")
    document = json.loads(path.read_text(encoding="utf-8"))
    if document.get("artifact") != "frozen-right-extension-summary":
        raise ValueError("unexpected frozen-summary artifact kind")
    if document.get("summary", {}).get("id") != "pair-principal-spectrum-v1":
        raise ValueError("this producer implements only pair-principal-spectrum-v1")
    if document.get("training_gate", {}).get("scope") != (
            "complete labeled parent catalogs at n=4 and n=5"):
        raise ValueError("unexpected frozen-summary training scope")
    return document


def make_training_report(levels: dict[int, tuple[int, ...]],
                         edges: dict[int, tuple[tuple[int, int, int], ...]],
                         summary_path: Path, summary_sha256: str) -> dict[str, object]:
    summary_document = validate_frozen_summary(summary_path, summary_sha256)
    level_reports = {}
    first_count_falsifier = None
    first_nonsymmetric_collision = None
    for n in (4, 5):
        extension_counts = Counter(parent for parent, _, _ in edges[n + 1])
        groups: dict[tuple[tuple[int, int, int], ...], list[int]] = {}
        for state in levels[n]:
            groups.setdefault(pair_principal_spectrum(state, n), []).append(state)

        group_rows = []
        nonsymmetric_pair_count = 0
        count_falsifier_count = 0
        collision_histogram: Counter[int] = Counter()
        for profile, members in sorted(groups.items()):
            members.sort()
            collision_histogram[len(members)] += 1
            behaviors = {extension_counts[state] for state in members}
            if len(behaviors) > 1:
                count_falsifier_count += 1
                if first_count_falsifier is None:
                    first = next(
                        (left, right) for left, right in itertools.combinations(members, 2)
                        if extension_counts[left] != extension_counts[right]
                    )
                    first_count_falsifier = {
                        "n": n,
                        "left": hex_mask(first[0], n),
                        "left_count": extension_counts[first[0]],
                        "right": hex_mask(first[1], n),
                        "right_count": extension_counts[first[1]],
                    }
            outside_pairs = []
            for left, right in itertools.combinations(members, 2):
                if right not in symmetry_orbit(left, n):
                    nonsymmetric_pair_count += 1
                    outside_pairs.append([hex_mask(left, n), hex_mask(right, n)])
                    if first_nonsymmetric_collision is None:
                        first_nonsymmetric_collision = {
                            "n": n,
                            "left": hex_mask(left, n),
                            "right": hex_mask(right, n),
                            "right_extension_count": extension_counts[left],
                        }
            group_rows.append({
                "profile": [list(entry) for entry in profile],
                "members": [hex_mask(state, n) for state in members],
                "right_extension_counts": {
                    hex_mask(state, n): extension_counts[state] for state in members
                },
                "outside_symmetry_pairs": outside_pairs,
            })
        level_reports[str(n)] = {
            "parent_count": len(levels[n]),
            "summary_count": len(groups),
            "summary_class_size_histogram": {
                str(size): count for size, count in sorted(collision_histogram.items())
            },
            "same_summary_count_falsifier_classes": count_falsifier_count,
            "nonsymmetric_same_summary_pair_count": nonsymmetric_pair_count,
            "groups": group_rows,
        }

    if first_count_falsifier is not None:
        outcome = "TRAINING-FAIL-COLLISION"
    elif first_nonsymmetric_collision is None:
        outcome = "TRAINING-FAIL-NONCOMPRESSION"
    else:
        outcome = "TRAINING-PASS"
    return {
        "schema_version": 1,
        "summary_artifact": str(summary_path),
        "summary_artifact_sha256": summary_sha256,
        "summary_id": summary_document["summary"]["id"],
        "scope": "complete labeled parent catalogs at n=4 and n=5",
        "outcome": outcome,
        "levels": level_reports,
        "first_count_falsifier": first_count_falsifier,
        "first_nonsymmetric_collision": first_nonsymmetric_collision,
        "held_out_n7_opened": False,
        "n7_outcomes_generated": False,
    }


def make_level(states: tuple[int, ...], n: int) -> dict[str, object]:
    state_hex = [hex_mask(state, n) for state in states]
    annotations = {
        hex_mask(state, n): state_annotations(state, n) for state in states
    }
    annotation_histogram = Counter(
        (
            row["cup_maximum"], row["cap_maximum"], row["strong_maximum"],
            row["decomposable"],
        )
        for row in annotations.values()
    )
    forbidden = [
        f"{pattern:04b}" for pattern in range(16)
        if not one_change(tuple(bool(pattern & (1 << shift))
                                for shift in range(3, -1, -1)))
    ]
    reflection_rows = symmetry_rows(states, n, reflect_color)
    reversal_rows = symmetry_rows(states, n, reverse_order)
    state_set = set(states)
    if {reflect_color(state, n) for state in states} != state_set:
        raise AssertionError("color reflection does not preserve the catalog")
    if {reverse_order(state, n) for state in states} != state_set:
        raise AssertionError("order reversal does not preserve the catalog")
    return {
        "n": n,
        "model_tier": MODEL,
        "catalog_kind": "complete labeled; no symmetry quotient",
        "triple_order": [list(triple) for triple in triples(n)],
        "hex_width": width(n),
        "state_count": len(states),
        "states_hex": state_hex,
        "states_sha256": sha256_lines(state_hex),
        "annotations": annotations,
        "annotations_sha256": canonical_sha256(annotations),
        "annotation_histogram": {
            f"cup={cup},cap={cap},strong={strong},decomposable={str(decomp).lower()}": count
            for (cup, cap, strong, decomp), count in sorted(annotation_histogram.items())
        },
        "decomposable_count": sum(row["decomposable"] for row in annotations.values()),
        "local_constraint_count": len(tuple(itertools.combinations(range(n), 4))),
        "inherited_constraint_count": len(tuple(itertools.combinations(range(n - 1), 4))),
        "first_appearing_constraint_count": len(tuple(
            itertools.combinations(range(n - 1), 3))),
        "minimal_forbidden_quadruple_words": forbidden,
        "symmetry_audit": {
            "quotient_applied": False,
            "actions": [
                {
                    "name": "color_reflection",
                    "definition": "complement every triple color",
                    "mapping_sha256": sha256_lines(reflection_rows),
                },
                {
                    "name": "order_reversal",
                    "definition": "i maps to n-1-i and every oriented triple flips",
                    "mapping_sha256": sha256_lines(reversal_rows),
                },
            ],
        },
    }


def make_edge_level(rows: tuple[tuple[int, int, int], ...],
                    old_n: int) -> dict[str, object]:
    new_n = old_n + 1
    edge_rows = [
        {
            "child": hex_mask(child, new_n),
            "new_pair_bits": f"{pair_mask:0{max(1, (len(pairs(old_n)) + 3) // 4)}x}",
            "parent": hex_mask(parent, old_n),
        }
        for parent, child, pair_mask in rows
    ]
    extension_counts = Counter(parent for parent, _, _ in rows)
    count_histogram = Counter(extension_counts.values())
    encoded_rows = [
        f"{row['parent']}>{row['child']}:{row['new_pair_bits']}" for row in edge_rows
    ]
    return {
        "old_n": old_n,
        "new_n": new_n,
        "restriction": "delete the rightmost vertex",
        "edge_count": len(edge_rows),
        "edges": edge_rows,
        "edges_sha256": sha256_lines(encoded_rows),
        "parent_extension_counts": {
            hex_mask(parent, old_n): extension_counts[parent]
            for parent in sorted(extension_counts)
        },
        "extension_count_histogram": {
            str(count): multiplicity for count, multiplicity in sorted(count_histogram.items())
        },
        "state_dependent_count_identity": {
            "lhs_child_count": len(edge_rows),
            "rhs_sum_parent_extension_counts": sum(extension_counts.values()),
            "is_compressed_recurrence": False,
        },
    }


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo, check=True, text=True, stdout=subprocess.PIPE)
    return completed.stdout.strip()


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n",
                         encoding="utf-8")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--max-n", type=int, default=6)
    parser.add_argument("--summary-candidate", type=Path)
    parser.add_argument("--summary-sha256")
    parser.add_argument("--training-output", type=Path)
    args = parser.parse_args()
    if not 4 <= args.max_n <= 6:
        parser.error("before the blind-profile release, --max-n must lie in [4, 6]")
    summary_options = (
        args.summary_candidate, args.summary_sha256, args.training_output
    )
    if any(value is not None for value in summary_options) and not all(
            value is not None for value in summary_options):
        parser.error("summary candidate, SHA-256, and training output are all required")
    if args.training_output is not None and args.max_n != 6:
        parser.error("the frozen training gate requires the hierarchy through n=6")

    started = time.perf_counter()
    levels, edges = enumerate_hierarchy(args.max_n)
    level_documents = {
        str(n): make_level(levels[n], n) for n in range(4, args.max_n + 1)
    }
    edge_documents = {
        f"{old_n}_to_{old_n + 1}": make_edge_level(edges[old_n + 1], old_n)
        for old_n in range(3, args.max_n)
    }
    catalog = {
        "schema_version": SCHEMA_VERSION,
        "model_tier": MODEL,
        "bounds": {"min_n": 4, "max_n": args.max_n},
        "labeled": True,
        "symmetry_quotient": False,
        "levels": level_documents,
        "rightmost_extensions": edge_documents,
    }
    catalog_path = args.output_dir / "catalog.json"
    write_atomic(catalog_path, catalog)
    if args.training_output is not None:
        training_report = make_training_report(
            levels, edges, args.summary_candidate, args.summary_sha256)
        write_atomic(args.training_output, training_report)

    usage = resource.getrusage(resource.RUSAGE_SELF)
    repo = Path(__file__).resolve().parent.parent
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "producer": "scripts/enumerate_local_constraint_hierarchy.py",
        "revision": git_revision(repo),
        "model_tier": MODEL,
        "bounds": catalog["bounds"],
        "catalog": str(catalog_path),
        "catalog_sha256": hashlib.sha256(catalog_path.read_bytes()).hexdigest(),
        "state_counts": {key: value["state_count"]
                         for key, value in level_documents.items()},
        "decomposable_counts": {key: value["decomposable_count"]
                                for key, value in level_documents.items()},
        "edge_counts": {key: value["edge_count"]
                        for key, value in edge_documents.items()},
        "resources": {
            "wall_seconds": time.perf_counter() - started,
            "user_cpu_seconds": usage.ru_utime,
            "system_cpu_seconds": usage.ru_stime,
            "peak_rss_kib": usage.ru_maxrss,
            "python": sys.version.split()[0],
            "platform": platform.platform(),
        },
        "claim_boundary": [
            "complete only for labeled abstract OneChangeOn colorings at the stated bounds",
            "does not establish sweep realizability or straight-line realizability",
            "the state-dependent extension sum is not a compressed recurrence",
        ],
    }
    write_atomic(args.output_dir / "manifest.json", manifest)
    print(args.output_dir / "manifest.json")


if __name__ == "__main__":
    main()
