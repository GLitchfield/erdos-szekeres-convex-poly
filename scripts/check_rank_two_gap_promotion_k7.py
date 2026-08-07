#!/usr/bin/env python3
"""Independently replay the rank-two root-gap promotion census.

This checker imports no new producer code.  It uses the independent
row-height rank implementation from check_allocated_span_pascal_demand and
reconstructs hidden gaps directly as consecutive vertices within a child,
rather than decomposing the parent membership word into runs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

import check_allocated_span_pascal_demand as independent


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return completed.stdout.strip()


def is_ancestor(repo: Path, ancestor: str, descendant: str) -> bool:
    completed = subprocess.run(
        [
            "git",
            "--git-dir=.git-data",
            "--work-tree=.",
            "merge-base",
            "--is-ancestor",
            ancestor,
            descendant,
        ],
        cwd=repo,
        check=False,
    )
    return completed.returncode == 0


def direct_promoted_groups(
    local: dict[tuple[int, int, int], int],
    support: int,
    lower: int,
    maximum_n: int,
) -> tuple[
    tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...],
    tuple[dict[str, object], ...],
]:
    vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    upper = support ^ lower
    transitions = tuple(
        (left, right)
        for left, right in zip(vertices, vertices[1:])
        if bool(lower & (1 << left)) != bool(lower & (1 << right))
    )
    matched: dict[int, set[tuple[int, int]]] = {0: set(), 1: set()}
    additions: defaultdict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    records: list[dict[str, object]] = []

    for child_is_lower, child_mask in ((True, lower), (False, upper)):
        child_vertices = tuple(
            vertex for vertex in vertices if child_mask & (1 << vertex)
        )
        other_mask = upper if child_is_lower else lower
        for left, right in zip(child_vertices, child_vertices[1:]):
            intervening = tuple(
                vertex
                for vertex in vertices
                if left < vertex < right and other_mask & (1 << vertex)
            )
            if not intervening:
                continue
            entering_transition = intervening[-1], right
            if entering_transition not in transitions:
                raise AssertionError("direct hidden gap lacks entering transition")
            color = 0 if child_is_lower else 1
            rank = local[color, left, right]
            if rank < 3:
                raise AssertionError("direct hidden gap lacks forced rank three")
            if entering_transition in matched[color]:
                raise AssertionError("duplicate direct same-color promotion")
            matched[color].add(entering_transition)
            additions[color, rank].append((left, right))
            records.append(
                {
                    "color": color,
                    "hidden_gap": [left, right],
                    "intervening_run": list(intervening),
                    "matched_transition": list(entering_transition),
                    "exact_ambient_rank": rank,
                }
            )

    collected: defaultdict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    for color, rank, frontier in independent.groups(
        local, support, lower, maximum_n
    ):
        collected[color, rank].extend(frontier)
    for color in (0, 1):
        collected[color, 2].extend(
            transition for transition in transitions if transition not in matched[color]
        )
    for key, gaps in additions.items():
        collected[key].extend(gaps)
    groups = tuple(
        (color, rank, tuple(sorted(spans)))
        for (color, rank), spans in sorted(collected.items())
        if spans
    )
    records.sort(key=lambda record: tuple(record["matched_transition"]))
    return groups, tuple(records)


def compact_example(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    spans: tuple[tuple[int, int], ...],
    promotions: tuple[dict[str, object], ...],
    capacity: int,
) -> dict[str, object]:
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "color": "cup" if color else "cap",
        "rank": rank,
        "spans": [list(span) for span in spans],
        "capacity": capacity,
        "promotions": list(promotions),
    }


def replay(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    strong_size = 7
    machine = independent.Replay(maximum_n, strong_size)
    full = (1 << maximum_n) - 1
    machine.colorings(full)
    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    by_rank: dict[tuple[int, int], Counter[str]] = {}
    first_capacity_failure = None
    first_candidate_failure = None
    digest = hashlib.sha256()
    stopped = False

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, full + 1):
            if support.bit_count() != size:
                continue
            vertices = tuple(
                vertex for vertex in range(maximum_n) if support & (1 << vertex)
            )
            for lower in independent.proper_parts(support):
                upper = support ^ lower
                fixed = machine.crossing(support, lower)
                for lower_bits in machine.colorings(lower):
                    for upper_bits in machine.colorings(upper):
                        bits = lower_bits | upper_bits | fixed
                        row["root_contexts"] += 1
                        local = machine.ranks(bits, support)
                        if local is None:
                            row["terminal_contexts"] += 1
                            continue
                        row["open_contexts"] += 1
                        groups, promotions = direct_promoted_groups(
                            local, support, lower, maximum_n
                        )
                        row["promotion_records"] += len(promotions)
                        record_groups = []
                        for color, rank, spans in groups:
                            row["adjusted_group_checks"] += 1
                            rank_row = by_rank.setdefault((color, rank), Counter())
                            rank_row["group_count"] += 1
                            rank_row["maximum_size"] = max(
                                rank_row["maximum_size"], len(spans)
                            )
                            capacity = independent.pascal(strong_size - 2, rank - 1)
                            capacity_ok = len(spans) <= capacity
                            candidates, _, _, _ = (
                                independent.replay_transition_candidates(
                                    local,
                                    vertices,
                                    spans,
                                    color,
                                    rank,
                                    strong_size,
                                )
                            )
                            candidate_ok = independent.replay_distinct_representatives(
                                candidates
                            )
                            if not capacity_ok:
                                row["capacity_failures"] += 1
                                rank_row["capacity_failures"] += 1
                                if first_capacity_failure is None:
                                    first_capacity_failure = compact_example(
                                        support,
                                        lower,
                                        bits,
                                        color,
                                        rank,
                                        spans,
                                        promotions,
                                        capacity,
                                    )
                            if not candidate_ok:
                                row["candidate_failures"] += 1
                                rank_row["candidate_failures"] += 1
                                if first_candidate_failure is None:
                                    columns = strong_size - rank - 1
                                    first_candidate_failure = {
                                        **compact_example(
                                            support,
                                            lower,
                                            bits,
                                            color,
                                            rank,
                                            spans,
                                            promotions,
                                            capacity,
                                        ),
                                        "candidate_ideals_hex": [
                                            [
                                                independent.height_mask_hex(
                                                    ideal, columns
                                                )
                                                for ideal in family
                                            ]
                                            for family in candidates
                                        ],
                                    }
                            record_groups.append(
                                [
                                    color,
                                    rank,
                                    [list(span) for span in spans],
                                    capacity_ok,
                                    candidate_ok,
                                ]
                            )
                        digest.update(
                            json.dumps(
                                [
                                    support,
                                    lower,
                                    bits,
                                    record_groups,
                                    promotions,
                                ],
                                separators=(",", ":"),
                                sort_keys=True,
                            ).encode()
                        )
                        digest.update(b"\n")
                        if stop_on_failure and (
                            first_capacity_failure is not None
                            or first_candidate_failure is not None
                        ):
                            stopped = True
                            break
                    if stopped:
                        break
                if stopped:
                    break
            if stopped:
                break
        by_size[str(size)] = row
        totals.update(row)
        if stopped:
            break

    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                key: dict(sorted(row.items())) for key, row in by_size.items()
            },
            "by_color_rank": {
                f"{'cup' if color else 'cap'}-{rank}": dict(sorted(row.items()))
                for (color, rank), row in sorted(by_rank.items())
            },
            "analyzed_local_states": len(machine.analysis_cache),
        },
        "first_capacity_failure": first_capacity_failure,
        "first_candidate_failure": first_candidate_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def validate_sources(repo: Path, manifest: dict[str, object]) -> None:
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise SystemExit(f"source digest mismatch: {source['path']}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    manifest = json.loads(args.manifest.read_text())
    validate_sources(repo, manifest)
    if not is_ancestor(
        repo, manifest["generation_base_revision"], git_revision(repo)
    ):
        raise SystemExit("generation base revision is not an ancestor of HEAD")
    if args.source_only:
        print("source digests and base revision verified")
        return
    census = manifest["census"]
    actual = replay(census["maximum_n"], census["stop_on_failure"])
    if actual != census:
        raise SystemExit("independent replay does not match manifest census")
    print("independent rank-two gap-promotion replay passed")


if __name__ == "__main__":
    main()
