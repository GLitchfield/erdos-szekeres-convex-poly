#!/usr/bin/env python3
"""Generate a singleton-lower signotope CNF with forced cup/cap subsets.

Every triple through the marked root is fixed by the deep-below crossing law.
Repeated ``--force-cup`` and ``--force-cap`` arguments name comma-separated
vertex sets. This is a bounded falsification aid, not a Lean proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from generate_rooted_cup_blocks_state_sat import forced_root_units
from generate_signotope_state_sat import generate, git_revision, triples, write_atomic


def parse_vertex_set(text: str, n: int) -> tuple[int, ...]:
    try:
        vertices = tuple(int(item) for item in text.split(",") if item)
    except ValueError as error:
        raise argparse.ArgumentTypeError("vertex sets must be comma-separated integers") from error
    if len(set(vertices)) != len(vertices):
        raise argparse.ArgumentTypeError("a forced set cannot repeat a vertex")
    if not vertices or min(vertices) < 0 or max(vertices) >= n:
        raise argparse.ArgumentTypeError("a forced set contains an out-of-range vertex")
    return tuple(sorted(vertices))


def forced_set_units(
    sets: list[tuple[int, ...]],
    variables: dict[tuple[int, int, int], int],
    value: bool,
) -> list[list[int]]:
    return [
        [variables[triple] if value else -variables[triple]]
        for vertices in sets
        for triple in triples(vertices)
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--root", type=int, required=True)
    parser.add_argument("--cap", type=int, required=True)
    parser.add_argument("--cup", type=int, required=True)
    parser.add_argument("--strong", type=int, required=True)
    parser.add_argument("--force-cap", action="append", default=[])
    parser.add_argument("--force-cup", action="append", default=[])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.n < 3:
        parser.error("n must be at least three")
    if not 0 <= args.root < args.n:
        parser.error("root must be a vertex of the ambient order")
    if min(args.cap, args.cup, args.strong) < 3:
        parser.error("forbidden outcome sizes must be at least three")
    if max(args.cap, args.cup, args.strong) > args.n:
        parser.error("forbidden outcome sizes cannot exceed the ambient size")
    try:
        forced_caps = [parse_vertex_set(text, args.n) for text in args.force_cap]
        forced_cups = [parse_vertex_set(text, args.n) for text in args.force_cup]
    except argparse.ArgumentTypeError as error:
        parser.error(str(error))
    if any(args.root in vertices for vertices in (*forced_caps, *forced_cups)):
        parser.error("forced upper sets cannot contain the singleton lower root")

    all_triples, clauses, _, counts, pattern_count = generate(
        args.n, args.cap, args.cup, args.strong
    )
    variables = {triple: index + 1 for index, triple in enumerate(all_triples)}
    left_size = args.root
    right_size = args.n - args.root - 1
    root, root_units = forced_root_units(left_size, right_size, variables)
    cap_units = forced_set_units(forced_caps, variables, False)
    cup_units = forced_set_units(forced_cups, variables, True)
    clauses.extend(root_units)
    clauses.extend(cap_units)
    clauses.extend(cup_units)
    counts = {
        **counts,
        "root_crossing_units": len(root_units),
        "forced_cap_units": len(cap_units),
        "forced_cup_units": len(cup_units),
    }

    cnf_lines = [f"p cnf {len(all_triples)} {len(clauses)}"]
    cnf_lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    cnf = "\n".join(cnf_lines) + "\n"
    write_atomic(args.output, cnf)
    repo = Path(__file__).resolve().parent.parent
    upper = [vertex for vertex in range(args.n) if vertex != root]
    manifest = {
        "schema_version": 1,
        "generator": "scripts/generate_rooted_forced_sets_state_sat.py",
        "revision": git_revision(repo),
        "n": args.n,
        "root": root,
        "cap": args.cap,
        "cup": args.cup,
        "strong": args.strong,
        "variables": len(all_triples),
        "clauses": len(clauses),
        "clause_counts": counts,
        "strong_pattern_count": pattern_count,
        "triple_order": (
            "lexicographic combinations(range(n), 3); DIMACS variables are one-based"
        ),
        "forced_blocks": [list(vertices) for vertices in forced_cups],
        "forced_cap_blocks": [list(vertices) for vertices in forced_caps],
        "forced_singleton_lower_split": {"root": root, "upper": upper},
        "cnf": str(args.output),
        "cnf_sha256": hashlib.sha256(cnf.encode()).hexdigest(),
    }
    write_atomic(
        args.output.with_suffix(args.output.suffix + ".json"),
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
    )
    print(args.output)


if __name__ == "__main__":
    main()
