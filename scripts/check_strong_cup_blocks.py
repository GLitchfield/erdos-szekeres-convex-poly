#!/usr/bin/env python3
"""Falsify normalized strong-six plus ordered-block gates.

The finite coloring is constrained by the rank-three one-change law and
avoids the requested cap, cup, and strong outcomes.  One consecutive block is
a strong six with a prescribed four-bit middle-color word; the other is a
four-cup.  All sixteen middle words and both block orders are checked.

This is a deterministic route-selection experiment, not a proof producer.
UNSAT results remain advisory until their consequences compile in Lean.
"""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path

from generate_signotope_state_sat import generate, triples, write_atomic


def strong_units(variables, strong_vertices, word):
    units: list[list[int]] = []
    position = {vertex: index for index, vertex in enumerate(strong_vertices)}
    for triple in triples(strong_vertices):
        middle_position = position[triple[1]]
        if not 1 <= middle_position <= 4:
            raise AssertionError("a triple middle must be internal to the block")
        variable = variables[triple]
        units.append([variable if word[middle_position - 1] else -variable])
    return units


def write_cnf(path: Path, variable_count: int, clauses) -> None:
    lines = [f"p cnf {variable_count} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    write_atomic(path, "\n".join(lines) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--cap", type=int, default=5)
    parser.add_argument("--cup", type=int, default=6)
    parser.add_argument("--strong", type=int, default=7)
    parser.add_argument("--other-size", type=int, default=4)
    parser.add_argument(
        "--other-mode", choices=("cup", "cap-free"), default="cup"
    )
    parser.add_argument("--side-cap", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument(
        "--solver", type=Path, default=Path("/tmp/cadical-local/usr/bin/cadical")
    )
    args = parser.parse_args()
    if not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")
    args.output_dir.mkdir(parents=True, exist_ok=True)

    n = 6 + args.other_size
    all_triples, base, _, counts, pattern_count = generate(
        n, args.cap, args.cup, args.strong
    )
    variables = {triple: index + 1 for index, triple in enumerate(all_triples)}
    records = []
    start = time.monotonic()
    for order in ("strong-cup", "cup-strong"):
        if order == "strong-cup":
            strong_vertices = tuple(range(6))
            other_vertices = tuple(range(6, n))
        else:
            other_vertices = tuple(range(args.other_size))
            strong_vertices = tuple(range(args.other_size, n))
        for word in itertools.product((False, True), repeat=4):
            label = "".join("L" if bit else "R" for bit in word)
            cnf = args.output_dir / f"{order}-{label}.cnf"
            clauses = [*base, *strong_units(variables, strong_vertices, word)]
            if args.other_mode == "cup":
                clauses.extend([variables[triple]]
                               for triple in triples(other_vertices))
            else:
                for block in (strong_vertices, other_vertices):
                    clauses.extend(
                        [variables[triple] for triple in triples(vertices)]
                        for vertices in itertools.combinations(block, args.side_cap)
                    )
            write_cnf(cnf, len(all_triples), clauses)
            model = cnf.with_suffix(".model")
            completed = subprocess.run(
                [str(args.solver), "-q", "--seed=0", "-t", str(args.timeout),
                 "-w", str(model), str(cnf)],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=args.timeout + 5,
            )
            result = {10: "SAT", 20: "UNSAT"}.get(
                completed.returncode, "LIMIT"
            )
            records.append({"order": order, "word": label, "result": result})

    summary = {
        "schema_version": 1,
        "generator": "scripts/check_strong_cup_blocks.py",
        "parameters": {
            "cap": args.cap,
            "cup": args.cup,
            "strong": args.strong,
            "other_size": args.other_size,
            "other_mode": args.other_mode,
            "side_cap": args.side_cap,
            "timeout": args.timeout,
        },
        "base_clause_counts": counts,
        "strong_pattern_count": pattern_count,
        "records": records,
        "elapsed_seconds": round(time.monotonic() - start, 3),
    }
    write_atomic(args.output_dir / "summary.json",
                 json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "SAT": sum(record["result"] == "SAT" for record in records),
        "UNSAT": sum(record["result"] == "UNSAT" for record in records),
        "LIMIT": sum(record["result"] == "LIMIT" for record in records),
        "elapsed_seconds": summary["elapsed_seconds"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
