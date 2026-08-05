#!/usr/bin/env python3
"""Check the two-side contract with an eager middle-determinacy encoding.

For every pair of triples with the same middle vertex, one shared auxiliary
variable records whether their colors differ.  A set is a strong polygon iff
all its same-middle comparisons agree, so one clause per candidate set forces
at least one shared difference.  This replaces lazy whole-pattern blockers.

SAT models are validated directly from the triple assignment.  UNSAT remains
computational evidence unless a proof certificate is independently checked.
"""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import time
from pathlib import Path

from check_two_cap_free_sides import (
    base_instance,
    parse_model,
    validate_assignment,
    write_cnf,
)
from generate_signotope_state_sat import git_revision, triples, write_atomic


Triple = tuple[int, int, int]
Comparison = tuple[Triple, Triple]


def comparison_key(left: Triple, right: Triple) -> Comparison:
    return (left, right) if left < right else (right, left)


def add_xor_definition(
        clauses: list[list[int]], difference: int, left: int, right: int
) -> None:
    """Add `difference ↔ (left XOR right)` to a CNF clause list."""
    clauses.extend((
        [-left, -right, -difference],
        [left, right, -difference],
        [left, -right, difference],
        [-left, right, difference],
    ))


def middle_comparisons(vertices: tuple[int, ...]) -> list[Comparison]:
    comparisons = []
    for middle_index in range(1, len(vertices) - 1):
        middle = vertices[middle_index]
        centered = [
            (left, middle, right)
            for left in vertices[:middle_index]
            for right in vertices[middle_index + 1:]
        ]
        anchor = centered[0]
        comparisons.extend(comparison_key(anchor, other)
                           for other in centered[1:])
    return comparisons


def solve(args: argparse.Namespace) -> None:
    start = time.monotonic()
    all_triples, variables, clauses, counts = base_instance(
        args.n, args.cut, args.side_cap, args.cap, args.cup)

    comparison_variables: dict[Comparison, int] = {}
    strong_blockers: list[list[int]] = []
    next_variable = len(all_triples) + 1
    for vertices in itertools.combinations(range(args.n), args.strong):
        blocker = []
        for comparison in middle_comparisons(vertices):
            if comparison not in comparison_variables:
                comparison_variables[comparison] = next_variable
                next_variable += 1
            blocker.append(comparison_variables[comparison])
        strong_blockers.append(blocker)

    xor_clauses = []
    for (left, right), difference in comparison_variables.items():
        add_xor_definition(
            xor_clauses, difference, variables[left], variables[right])
    clauses.extend(xor_clauses)
    clauses.extend(strong_blockers)

    total_variables = next_variable - 1
    sha256 = write_cnf(args.output, total_variables, clauses, ())
    model_path = args.output.with_suffix(args.output.suffix + ".model")
    remaining = args.timeout - (time.monotonic() - start)
    if remaining <= 0:
        completed = None
        result = "LIMIT"
    else:
        completed = subprocess.run(
            [str(args.solver), "-q", "--seed=0", "-t",
             str(max(1, int(remaining))), "-w", str(model_path),
             str(args.output)],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=remaining + 5)
        result = "SAT" if completed.returncode == 10 else (
            "UNSAT" if completed.returncode == 20 else "LIMIT")

    validation = None
    model_json = None
    if result == "SAT":
        model = parse_model(model_path, total_variables)
        triple_model = {index for index in model if index <= len(all_triples)}
        validation = validate_assignment(
            args.n, args.cut, args.side_cap, args.cap, args.cup,
            args.strong, triple_model, variables, False)
        xor_valid = all(
            (difference in model) ==
            ((variables[left] in model) != (variables[right] in model))
            for (left, right), difference in comparison_variables.items())
        validation["xor_auxiliaries_valid"] = xor_valid
        validation["valid"] = validation["valid"] and xor_valid
        if not validation["valid"]:
            raise RuntimeError(f"independent model validation failed: {validation}")
        model_json = args.output.with_suffix(args.output.suffix + ".model.json")
        write_atomic(model_json, json.dumps({
            "schema_version": 1,
            "n": args.n,
            "cut": args.cut,
            "left_triples": [list(all_triples[index - 1])
                             for index in sorted(triple_model)],
            "validation": validation,
        }, indent=2, sort_keys=True) + "\n")

    elapsed = time.monotonic() - start
    manifest = {
        "schema_version": 1,
        "generator": "scripts/check_two_cap_free_sides_middle.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "parameters": {key: getattr(args, key) for key in
                       ("n", "cut", "side_cap", "cap", "cup", "strong",
                        "timeout")},
        "solver": str(args.solver),
        "result": result,
        "triple_variables": len(all_triples),
        "comparison_variables": len(comparison_variables),
        "variables": total_variables,
        "base_clause_counts": counts,
        "xor_clauses": len(xor_clauses),
        "strong_blockers": len(strong_blockers),
        "clauses": len(clauses),
        "elapsed_seconds": round(elapsed, 3),
        "cnf": str(args.output),
        "cnf_sha256": sha256,
        "model_json": str(model_json) if model_json else None,
        "validation": validation,
        "solver_output_tail": completed.stdout[-2000:] if completed else "",
    }
    write_atomic(args.output.with_suffix(args.output.suffix + ".json"),
                 json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "result": result,
        "variables": total_variables,
        "clauses": len(clauses),
        "strong_blockers": len(strong_blockers),
        "elapsed_seconds": manifest["elapsed_seconds"],
        "validation": validation,
    }))
    raise SystemExit(10 if result == "SAT" else 20 if result == "UNSAT" else 1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--cut", type=int, required=True)
    parser.add_argument("--side-cap", type=int, default=4)
    parser.add_argument("--cap", type=int, default=5)
    parser.add_argument("--cup", type=int, default=6)
    parser.add_argument("--strong", type=int, default=7)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--solver", type=Path,
                        default=Path("/tmp/cadical-local/usr/bin/cadical"))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 0 < args.cut < args.n:
        parser.error("cut must lie strictly between zero and n")
    if min(args.side_cap, args.cap, args.cup, args.strong) < 3:
        parser.error("all forbidden sizes must be at least three")
    if max(args.side_cap, args.cap, args.cup, args.strong) > args.n:
        parser.error("forbidden sizes cannot exceed n")
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    if not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")
    solve(args)


if __name__ == "__main__":
    main()
