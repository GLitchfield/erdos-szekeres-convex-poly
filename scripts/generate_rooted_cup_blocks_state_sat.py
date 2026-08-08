#!/usr/bin/env python3
"""Generate the centered singleton-root cup-block gate as a bounded CNF.

The vertices are ordered as a left cup block, the singleton lower root, and a
right cup block.  Every triple through the root is fixed by the deep-below
crossing law.  This is a falsification aid only: UNSAT is not a completed
project result until the gate is proved in Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from generate_signotope_state_sat import generate, git_revision, triples, write_atomic


def forced_root_units(
    left: int, right: int, variables: dict[tuple[int, int, int], int]
) -> tuple[int, list[list[int]]]:
    """Return the centered root and its deep-below unit clauses."""
    root = left
    n = left + 1 + right
    units: list[list[int]] = []
    for triple in triples(range(n)):
        if root not in triple:
            continue
        variable = variables[triple]
        # The singleton is the lower child.  A crossing triple is left exactly
        # when its middle vertex is lower, which here means `triple[1] = root`.
        units.append([variable if triple[1] == root else -variable])
    return root, units


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--left", type=int, required=True)
    parser.add_argument("--right", type=int, required=True)
    parser.add_argument("--cap", type=int, required=True)
    parser.add_argument("--cup", type=int, required=True)
    parser.add_argument("--strong", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if min(args.left, args.right) < 0:
        parser.error("block sizes must be nonnegative")
    n = args.left + 1 + args.right
    if min(args.cap, args.cup, args.strong) < 3:
        parser.error("forbidden outcome sizes must be at least three")
    if max(args.cap, args.cup, args.strong) > n:
        parser.error("forbidden outcome sizes cannot exceed the ambient size")

    all_triples, clauses, _, counts, pattern_count = generate(
        n, args.cap, args.cup, args.strong
    )
    variables = {triple: index + 1 for index, triple in enumerate(all_triples)}
    root, root_units = forced_root_units(args.left, args.right, variables)
    left_vertices = tuple(range(args.left))
    right_vertices = tuple(range(root + 1, n))
    block_triples = (*triples(left_vertices), *triples(right_vertices))
    clauses.extend([variables[triple]] for triple in block_triples)
    clauses.extend(root_units)
    counts = {
        **counts,
        "cup_block_units": len(block_triples),
        "root_crossing_units": len(root_units),
    }

    cnf_lines = [f"p cnf {len(all_triples)} {len(clauses)}"]
    cnf_lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    cnf = "\n".join(cnf_lines) + "\n"
    write_atomic(args.output, cnf)
    repo = Path(__file__).resolve().parent.parent
    manifest = {
        "schema_version": 1,
        "generator": "scripts/generate_rooted_cup_blocks_state_sat.py",
        "revision": git_revision(repo),
        "n": n,
        "left": args.left,
        "right": args.right,
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
        "forced_blocks": [list(left_vertices), list(right_vertices)],
        "forced_singleton_lower_split": {
            "root": root,
            "upper": [*left_vertices, *right_vertices],
        },
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
