#!/usr/bin/env python3
"""Independently check a complete local OneChange hierarchy catalog.

This checker deliberately does not import the producer.  Through six vertices
it scans the entire Boolean cube of triple colorings, then derives rightmost
restriction edges from each accepted child.  It also replays four corruptions
against the already reconstructed expected document.
"""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import resource
import sys
import time


MODEL = "complete labeled abstract OneChangeOn triple colorings"
EXPECTED_COUNTS = {4: 8, 5: 62, 6: 908}


class VerificationError(Exception):
    pass


def all_triples(n: int) -> tuple[tuple[int, int, int], ...]:
    result: list[tuple[int, int, int]] = []
    for first in range(n):
        for second in range(first + 1, n):
            for third in range(second + 1, n):
                result.append((first, second, third))
    return tuple(result)


def all_pairs(n: int) -> tuple[tuple[int, int], ...]:
    return tuple((first, second) for first in range(n)
                 for second in range(first + 1, n))


def at_most_one_change(word: tuple[bool, ...]) -> bool:
    changes = 0
    previous = word[0]
    for value in word[1:]:
        if value != previous:
            changes += 1
            if changes > 1:
                return False
        previous = value
    return True


def digest_lines(lines: list[str]) -> str:
    payload = bytearray()
    for line in lines:
        payload.extend(line.encode())
        payload.append(10)
    return hashlib.sha256(payload).hexdigest()


def digest_json(value: object) -> str:
    payload = json.dumps(value, separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(payload.encode()).hexdigest()


def hex_width(n: int) -> int:
    return max(1, (len(all_triples(n)) + 3) // 4)


def show(mask: int, n: int) -> str:
    return format(mask, f"0{hex_width(n)}x")


def valid_coloring(mask: int, n: int) -> bool:
    position = {triple: index for index, triple in enumerate(all_triples(n))}
    for a, b, c, d in itertools.combinations(range(n), 4):
        sequence = (
            (a, b, c),
            (a, b, d),
            (a, c, d),
            (b, c, d),
        )
        word = tuple(bool(mask & (1 << position[triple])) for triple in sequence)
        if not at_most_one_change(word):
            return False
    return True


def exhaustive_level(n: int) -> tuple[int, ...]:
    return tuple(mask for mask in range(1 << len(all_triples(n)))
                 if valid_coloring(mask, n))


def restrict_rightmost(child: int, n: int) -> tuple[int, int]:
    """Recover the unique old coloring and colors on pairs incident to n-1."""
    old_n = n - 1
    child_position = {
        triple: index for index, triple in enumerate(all_triples(n))
    }
    parent = 0
    for index, triple in enumerate(all_triples(old_n)):
        parent |= int(bool(child & (1 << child_position[triple]))) << index
    pair_mask = 0
    for index, (a, b) in enumerate(all_pairs(old_n)):
        triple = (a, b, old_n)
        pair_mask |= int(bool(child & (1 << child_position[triple]))) << index
    return parent, pair_mask


def get_color(mask: int, position: dict[tuple[int, int, int], int],
              a: int, b: int, c: int) -> bool:
    return bool(mask & (1 << position[a, b, c]))


def monochrome(mask: int, position: dict[tuple[int, int, int], int],
               vertices: tuple[int, ...], value: bool) -> bool:
    for a, b, c in itertools.combinations(vertices, 3):
        if get_color(mask, position, a, b, c) != value:
            return False
    return True


def strong(mask: int, position: dict[tuple[int, int, int], int],
           vertices: tuple[int, ...]) -> bool:
    for a, b, c, d in itertools.combinations(vertices, 4):
        if get_color(mask, position, a, b, c) != get_color(mask, position, a, b, d):
            return False
        if get_color(mask, position, a, c, d) != get_color(mask, position, b, c, d):
            return False
    return True


def largest(n: int, predicate) -> int:
    for size in reversed(range(1, n + 1)):
        for vertices in itertools.combinations(range(n), size):
            if predicate(vertices):
                return size
    raise AssertionError("unreachable")


def decomposable(mask: int, n: int) -> bool:
    """Independent subset-combination recursion for directed deep-below trees."""
    triple_list = all_triples(n)
    position = {triple: index for index, triple in enumerate(triple_list)}

    @lru_cache(maxsize=None)
    def recurse(vertices: tuple[int, ...]) -> bool:
        if len(vertices) < 2:
            return True
        vertex_set = frozenset(vertices)
        for lower_size in range(1, len(vertices)):
            for lower_tuple in itertools.combinations(vertices, lower_size):
                lower = frozenset(lower_tuple)
                upper = vertex_set - lower
                good = True
                for a, b, c in itertools.combinations(vertices, 3):
                    membership = (a in lower, b in lower, c in lower)
                    if all(membership) or not any(membership):
                        continue
                    if get_color(mask, position, a, b, c) != (b in lower):
                        good = False
                        break
                if good and recurse(tuple(sorted(lower))) and recurse(tuple(sorted(upper))):
                    return True
        return False

    return recurse(tuple(range(n)))


def annotate(mask: int, n: int) -> dict[str, object]:
    position = {triple: index for index, triple in enumerate(all_triples(n))}
    return {
        "cap_maximum": largest(
            n, lambda vertices: monochrome(mask, position, vertices, False)),
        "cup_maximum": largest(
            n, lambda vertices: monochrome(mask, position, vertices, True)),
        "decomposable": decomposable(mask, n),
        "strong_maximum": largest(
            n, lambda vertices: strong(mask, position, vertices)),
    }


def color_reflection(mask: int, n: int) -> int:
    answer = mask
    for index in range(len(all_triples(n))):
        answer ^= 1 << index
    return answer


def order_reversal(mask: int, n: int) -> int:
    ordered = all_triples(n)
    position = {triple: index for index, triple in enumerate(ordered)}
    answer = 0
    for destination, (a, b, c) in enumerate(ordered):
        source = (n - 1 - c, n - 1 - b, n - 1 - a)
        source_value = bool(mask & (1 << position[source]))
        if not source_value:
            answer |= 1 << destination
    return answer


def symmetry_digest(states: tuple[int, ...], n: int, transform) -> str:
    rows = [f"{show(state, n)}>{show(transform(state, n), n)}" for state in states]
    return digest_lines(rows)


def independent_pair_spectrum(mask: int, n: int) -> tuple[tuple[int, int, int], ...]:
    """Matrix-closure replay of the frozen pair-principal spectrum."""
    pair_list = all_pairs(n)
    pair_position = {pair: index for index, pair in enumerate(pair_list)}
    triple_position = {
        triple: index for index, triple in enumerate(all_triples(n))
    }
    relation = [[source == target for target in range(len(pair_list))]
                for source in range(len(pair_list))]
    for i, j, k in all_triples(n):
        ij = pair_position[i, j]
        ik = pair_position[i, k]
        jk = pair_position[j, k]
        is_left = bool(mask & (1 << triple_position[i, j, k]))
        if is_left:
            relation[jk][ik] = True
            relation[ik][ij] = True
        else:
            relation[ij][ik] = True
            relation[ik][jk] = True
    for middle in range(len(pair_list)):
        for source in range(len(pair_list)):
            if not relation[source][middle]:
                continue
            for target in range(len(pair_list)):
                relation[source][target] |= relation[middle][target]

    raw = []
    for current in range(len(pair_list)):
        scc = sum(relation[current][other] and relation[other][current]
                  for other in range(len(pair_list)))
        lower = sum(relation[other][current] for other in range(len(pair_list)))
        upper = sum(relation[current])
        raw.append((scc, lower, upper))
    raw_profile = tuple(sorted(raw))
    dual_profile = tuple(sorted((scc, upper, lower)
                                for scc, lower, upper in raw_profile))
    return min(raw_profile, dual_profile)


def independent_orbit(mask: int, n: int) -> frozenset[int]:
    orbit = {mask}
    changed = True
    while changed:
        changed = False
        for state in tuple(orbit):
            for image in (color_reflection(state, n), order_reversal(state, n)):
                if image not in orbit:
                    orbit.add(image)
                    changed = True
    return frozenset(orbit)


def validate_summary(path: Path, expected_sha256: str) -> dict[str, object]:
    actual_sha256 = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual_sha256 != expected_sha256:
        raise VerificationError("frozen summary SHA-256 mismatch")
    document = json.loads(path.read_text(encoding="utf-8"))
    if document.get("artifact") != "frozen-right-extension-summary":
        raise VerificationError("frozen summary has the wrong artifact kind")
    if document.get("summary", {}).get("id") != "pair-principal-spectrum-v1":
        raise VerificationError("unsupported frozen parent summary")
    if document.get("training_gate", {}).get("scope") != (
            "complete labeled parent catalogs at n=4 and n=5"):
        raise VerificationError("frozen summary has the wrong training scope")
    return document


def independent_training_report(levels: dict[int, tuple[int, ...]],
                                summary_path: Path,
                                summary_sha256: str) -> dict[str, object]:
    document = validate_summary(summary_path, summary_sha256)
    level_reports = {}
    first_falsifier = None
    first_nonsymmetric = None
    for n in (4, 5):
        child_level = levels[n + 1]
        extension_counts = Counter(
            restrict_rightmost(child, n + 1)[0] for child in child_level
        )
        grouped: dict[tuple[tuple[int, int, int], ...], list[int]] = {}
        for parent in levels[n]:
            key = independent_pair_spectrum(parent, n)
            grouped.setdefault(key, []).append(parent)

        class_sizes: Counter[int] = Counter()
        falsifier_classes = 0
        nonsymmetric_pair_count = 0
        group_rows = []
        for spectrum in sorted(grouped):
            members = sorted(grouped[spectrum])
            class_sizes[len(members)] += 1
            behavior_values = {extension_counts[parent] for parent in members}
            if len(behavior_values) > 1:
                falsifier_classes += 1
                for left, right in itertools.combinations(members, 2):
                    if extension_counts[left] != extension_counts[right]:
                        if first_falsifier is None:
                            first_falsifier = {
                                "n": n,
                                "left": show(left, n),
                                "left_count": extension_counts[left],
                                "right": show(right, n),
                                "right_count": extension_counts[right],
                            }
                        break
            outside = []
            for left, right in itertools.combinations(members, 2):
                if right not in independent_orbit(left, n):
                    nonsymmetric_pair_count += 1
                    outside.append([show(left, n), show(right, n)])
                    if first_nonsymmetric is None:
                        first_nonsymmetric = {
                            "n": n,
                            "left": show(left, n),
                            "right": show(right, n),
                            "right_extension_count": extension_counts[left],
                        }
            group_rows.append({
                "profile": [list(entry) for entry in spectrum],
                "members": [show(parent, n) for parent in members],
                "right_extension_counts": {
                    show(parent, n): extension_counts[parent] for parent in members
                },
                "outside_symmetry_pairs": outside,
            })
        level_reports[str(n)] = {
            "parent_count": len(levels[n]),
            "summary_count": len(grouped),
            "summary_class_size_histogram": {
                str(size): count for size, count in sorted(class_sizes.items())
            },
            "same_summary_count_falsifier_classes": falsifier_classes,
            "nonsymmetric_same_summary_pair_count": nonsymmetric_pair_count,
            "groups": group_rows,
        }

    if first_falsifier is not None:
        outcome = "TRAINING-FAIL-COLLISION"
    elif first_nonsymmetric is None:
        outcome = "TRAINING-FAIL-NONCOMPRESSION"
    else:
        outcome = "TRAINING-PASS"
    return {
        "schema_version": 1,
        "summary_artifact": str(summary_path),
        "summary_artifact_sha256": summary_sha256,
        "summary_id": document["summary"]["id"],
        "scope": "complete labeled parent catalogs at n=4 and n=5",
        "outcome": outcome,
        "levels": level_reports,
        "first_count_falsifier": first_falsifier,
        "first_nonsymmetric_collision": first_nonsymmetric,
        "held_out_n7_opened": False,
        "n7_outcomes_generated": False,
    }


def expected_level(states: tuple[int, ...], n: int) -> dict[str, object]:
    state_hex = [show(state, n) for state in states]
    annotations = {show(state, n): annotate(state, n) for state in states}
    histogram = Counter(
        (row["cup_maximum"], row["cap_maximum"], row["strong_maximum"],
         row["decomposable"])
        for row in annotations.values()
    )
    forbidden = []
    for pattern in range(16):
        word = tuple(bool(pattern & (1 << position))
                     for position in range(3, -1, -1))
        if not at_most_one_change(word):
            forbidden.append(format(pattern, "04b"))
    reflected = {color_reflection(state, n) for state in states}
    reversed_states = {order_reversal(state, n) for state in states}
    if reflected != set(states) or reversed_states != set(states):
        raise VerificationError(f"declared symmetries fail independently at n={n}")
    return {
        "n": n,
        "model_tier": MODEL,
        "catalog_kind": "complete labeled; no symmetry quotient",
        "triple_order": [list(triple) for triple in all_triples(n)],
        "hex_width": hex_width(n),
        "state_count": len(states),
        "states_hex": state_hex,
        "states_sha256": digest_lines(state_hex),
        "annotations": annotations,
        "annotations_sha256": digest_json(annotations),
        "annotation_histogram": {
            f"cup={cup},cap={cap},strong={strong},decomposable={str(decomp).lower()}": count
            for (cup, cap, strong, decomp), count in sorted(histogram.items())
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
                    "mapping_sha256": symmetry_digest(states, n, color_reflection),
                },
                {
                    "name": "order_reversal",
                    "definition": "i maps to n-1-i and every oriented triple flips",
                    "mapping_sha256": symmetry_digest(states, n, order_reversal),
                },
            ],
        },
    }


def expected_edges(children: tuple[int, ...], parent_states: tuple[int, ...],
                   old_n: int) -> dict[str, object]:
    new_n = old_n + 1
    parent_set = set(parent_states)
    raw_rows: list[tuple[int, int, int]] = []
    for child in children:
        parent, pair_mask = restrict_rightmost(child, new_n)
        if parent not in parent_set:
            raise VerificationError(f"rightmost restriction is invalid at n={new_n}")
        raw_rows.append((parent, child, pair_mask))
    raw_rows.sort(key=lambda row: (row[1], row[0], row[2]))
    pair_width = max(1, (len(all_pairs(old_n)) + 3) // 4)
    rows = [
        {
            "child": show(child, new_n),
            "new_pair_bits": format(pair_mask, f"0{pair_width}x"),
            "parent": show(parent, old_n),
        }
        for parent, child, pair_mask in raw_rows
    ]
    parent_counts = Counter(parent for parent, _, _ in raw_rows)
    distribution = Counter(parent_counts.values())
    return {
        "old_n": old_n,
        "new_n": new_n,
        "restriction": "delete the rightmost vertex",
        "edge_count": len(rows),
        "edges": rows,
        "edges_sha256": digest_lines([
            f"{row['parent']}>{row['child']}:{row['new_pair_bits']}" for row in rows
        ]),
        "parent_extension_counts": {
            show(parent, old_n): parent_counts[parent] for parent in sorted(parent_counts)
        },
        "extension_count_histogram": {
            str(count): multiplicity for count, multiplicity in sorted(distribution.items())
        },
        "state_dependent_count_identity": {
            "lhs_child_count": len(rows),
            "rhs_sum_parent_extension_counts": sum(parent_counts.values()),
            "is_compressed_recurrence": False,
        },
    }


def reconstruct(max_n: int) -> tuple[dict[str, object], dict[int, tuple[int, ...]]]:
    levels = {n: exhaustive_level(n) for n in range(3, max_n + 1)}
    for n, expected_count in EXPECTED_COUNTS.items():
        if n <= max_n and len(levels[n]) != expected_count:
            raise VerificationError(
                f"independent n={n} count {len(levels[n])} != {expected_count}")
    document = {
        "schema_version": 1,
        "model_tier": MODEL,
        "bounds": {"min_n": 4, "max_n": max_n},
        "labeled": True,
        "symmetry_quotient": False,
        "levels": {
            str(n): expected_level(levels[n], n) for n in range(4, max_n + 1)
        },
        "rightmost_extensions": {
            f"{old_n}_to_{old_n + 1}": expected_edges(
                levels[old_n + 1], levels[old_n], old_n)
            for old_n in range(3, max_n)
        },
    }
    return document, levels


def require_equal(actual: object, expected: object, label: str) -> None:
    if actual != expected:
        raise VerificationError(f"{label} differs from independent reconstruction")


def verify_document(actual: dict[str, object], expected: dict[str, object]) -> None:
    require_equal(actual, expected, "catalog")


def e3_regressions(levels: dict[int, tuple[int, ...]], paths: list[Path]) -> dict[str, object]:
    by_n = {}
    for path in paths:
        document = json.loads(path.read_text(encoding="utf-8"))
        by_n[document["n"]] = (path, document)
    rows = {}
    for n in (4, 5, 6):
        path, old = by_n[n]
        decomposable_states = [state for state in levels[n] if decomposable(state, n)]
        state_hex = [show(state, n) for state in decomposable_states]
        count_ok = len(decomposable_states) == old["distinct_coloring_count"]
        digest_ok = digest_lines(state_hex) == old["distinct_colorings_sha256"]
        annotation_rows = [annotate(state, n) for state in decomposable_states]
        histograms = {
            name: {
                str(value): count for value, count in sorted(Counter(
                    row[f"{name}_maximum"] for row in annotation_rows
                ).items())
            }
            for name in ("cup", "cap", "strong")
        }
        histograms_ok = all(
            histograms[name] == old[f"{name}_maximum_histogram"]
            for name in histograms
        )
        if not count_ok or not digest_ok or not histograms_ok:
            raise VerificationError(f"decomposable regression mismatch against {path}")
        rows[str(n)] = {
            "path": str(path),
            "count": len(decomposable_states),
            "states_sha256": digest_lines(state_hex),
            "count_matches": count_ok,
            "digest_matches": digest_ok,
            "annotation_histograms_match": histograms_ok,
        }
    return rows


def expect_rejection(name: str, altered: dict[str, object],
                     expected: dict[str, object]) -> dict[str, object]:
    try:
        verify_document(altered, expected)
    except VerificationError as exc:
        return {"name": name, "rejected": True, "reason": str(exc)}
    raise VerificationError(f"negative control {name} was incorrectly accepted")


def corruption_controls(catalog: dict[str, object],
                        expected: dict[str, object]) -> list[dict[str, object]]:
    controls: list[dict[str, object]] = []

    changed = deepcopy(catalog)
    changed["levels"]["4"]["states_hex"][0] = "2"
    controls.append(expect_rejection("changed-color", changed, expected))

    omitted = deepcopy(catalog)
    omitted["levels"]["6"]["states_hex"].pop()
    controls.append(expect_rejection("omitted-state", omitted, expected))

    false_symmetry = deepcopy(catalog)
    false_symmetry["levels"]["5"]["symmetry_audit"]["actions"][1][
        "mapping_sha256"] = "0" * 64
    controls.append(expect_rejection("false-symmetry", false_symmetry, expected))

    bad_edge = deepcopy(catalog)
    bad_edge["rightmost_extensions"]["5_to_6"]["edges"][0]["parent"] = "fff"
    controls.append(expect_rejection("corrupted-edge", bad_edge, expected))
    return controls


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n",
                         encoding="utf-8")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--producer-manifest", type=Path, required=True)
    parser.add_argument("--e3", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--summary-candidate", type=Path)
    parser.add_argument("--summary-sha256")
    parser.add_argument("--training-report", type=Path)
    args = parser.parse_args()
    if len(args.e3) != 3:
        parser.error("pass exactly three --e3 manifests for n=4,5,6")
    summary_options = (
        args.summary_candidate, args.summary_sha256, args.training_report
    )
    if any(value is not None for value in summary_options) and not all(
            value is not None for value in summary_options):
        parser.error("summary candidate, SHA-256, and training report are all required")

    started = time.perf_counter()
    actual = json.loads(args.catalog.read_text(encoding="utf-8"))
    if actual.get("bounds") != {"min_n": 4, "max_n": 6}:
        raise VerificationError("the admitted census checker requires bounds 4..6")
    expected, levels = reconstruct(6)
    verify_document(actual, expected)

    producer_manifest = json.loads(args.producer_manifest.read_text(encoding="utf-8"))
    catalog_digest = hashlib.sha256(args.catalog.read_bytes()).hexdigest()
    if producer_manifest.get("catalog_sha256") != catalog_digest:
        raise VerificationError("producer manifest catalog digest mismatch")
    regressions = e3_regressions(levels, args.e3)
    controls = corruption_controls(actual, expected)
    training_outcome = None
    training_report_sha256 = None
    if args.training_report is not None:
        expected_training = independent_training_report(
            levels, args.summary_candidate, args.summary_sha256)
        actual_training = json.loads(args.training_report.read_text(encoding="utf-8"))
        require_equal(actual_training, expected_training, "frozen-summary training report")
        training_outcome = expected_training["outcome"]
        training_report_sha256 = hashlib.sha256(
            args.training_report.read_bytes()).hexdigest()
    usage = resource.getrusage(resource.RUSAGE_SELF)
    report = {
        "schema_version": 1,
        "checker": "scripts/check_local_constraint_hierarchy.py",
        "model_tier": MODEL,
        "catalog": str(args.catalog),
        "catalog_sha256": catalog_digest,
        "producer_checker_agree": True,
        "state_counts": {str(n): len(levels[n]) for n in (4, 5, 6)},
        "edge_counts": {
            key: value["edge_count"]
            for key, value in expected["rightmost_extensions"].items()
        },
        "decomposable_regressions": regressions,
        "corruption_controls": controls,
        "frozen_summary_training": {
            "outcome": training_outcome,
            "report": str(args.training_report) if args.training_report else None,
            "report_sha256": training_report_sha256,
            "independently_replayed": args.training_report is not None,
        },
        "resources": {
            "wall_seconds": time.perf_counter() - started,
            "user_cpu_seconds": usage.ru_utime,
            "system_cpu_seconds": usage.ru_stime,
            "peak_rss_kib": usage.ru_maxrss,
            "python": sys.version.split()[0],
            "platform": platform.platform(),
        },
        "claim_boundary": [
            "checked computation at n=4,5,6 only",
            "abstract OneChangeOn states are not certified point configurations",
            "no compressed parent recurrence is established",
        ],
    }
    write_atomic(args.output, report)
    print(args.output)


if __name__ == "__main__":
    main()
