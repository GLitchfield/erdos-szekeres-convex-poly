#!/usr/bin/env python3
"""Test two disjoint `3+3` crossing strong sixes on an ordered `6+6` cut.

This is a deterministic route-selection experiment, not a proof producer.
SAT assignments are checked internally and can be replayed by the independent
checker. An UNSAT result is advisory without a checked proof certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import time
from pathlib import Path

from check_two_cap_free_sides import (
    base_instance,
    is_strong,
    parse_model,
    validate_assignment,
)
from generate_signotope_state_sat import (
    forbidden_assignment,
    git_revision,
    strong_patterns,
    triples,
    write_atomic,
)


N = 12
CUT = 6
FIRST = (0, 1, 2, 6, 7, 8)
SECOND = (3, 4, 5, 9, 10, 11)


def add_equality(clauses: list[list[int]], left: int, right: int) -> None:
    clauses.extend(([-left, right], [left, -right]))


def add_strong(clauses, variables, vertices) -> int:
    before = len(clauses)
    for i, j, k, l in itertools.combinations(vertices, 4):
        add_equality(clauses, variables[i, j, k], variables[i, j, l])
        add_equality(clauses, variables[i, k, l], variables[j, k, l])
    return len(clauses) - before


def write_cnf(path: Path, variable_count: int, clauses) -> str:
    content = f"p cnf {variable_count} {len(clauses)}\n"
    content += "".join(" ".join(map(str, clause)) + " 0\n" for clause in clauses)
    write_atomic(path, content)
    return hashlib.sha256(content.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument(
        "--solver", type=Path, default=Path("/tmp/cadical-local/usr/bin/cadical")
    )
    args = parser.parse_args()
    if not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")
    args.output.parent.mkdir(parents=True, exist_ok=True)

    start = time.monotonic()
    all_triples, variables, clauses, counts = base_instance(N, CUT, 4, 5, 6)
    fixed_strong = add_strong(clauses, variables, FIRST)
    fixed_strong += add_strong(clauses, variables, SECOND)
    no_strong_seven = 0
    local = triples(range(7))
    for vertices in itertools.combinations(range(N), 7):
        keys = tuple(tuple(vertices[index] for index in triple) for triple in local)
        for values in strong_patterns(7):
            clauses.append(forbidden_assignment(keys, values, variables))
            no_strong_seven += 1

    digest = write_cnf(args.output, len(all_triples), clauses)
    model_path = args.output.with_suffix(args.output.suffix + ".model")
    completed = subprocess.run(
        [str(args.solver), "-q", "--seed=0", "-t", str(args.timeout),
         "-w", str(model_path), str(args.output)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=args.timeout + 5,
    )
    result = {10: "SAT", 20: "UNSAT"}.get(completed.returncode, "LIMIT")
    validation = None
    if result == "SAT":
        model = parse_model(model_path, len(all_triples))
        validation = validate_assignment(N, CUT, 4, 5, 6, 7, model, variables, False)
        validation["first_strong"] = is_strong(FIRST, model, variables)
        validation["second_strong"] = is_strong(SECOND, model, variables)
        validation["valid"] = (
            validation["valid"]
            and validation["first_strong"]
            and validation["second_strong"]
        )
        if not validation["valid"]:
            raise RuntimeError(f"model validation failed: {validation}")

    manifest = {
        "schema_version": 1,
        "generator": "scripts/check_middle_split_pair.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "parameters": {"n": N, "cut": CUT, "timeout": args.timeout},
        "first": list(FIRST),
        "second": list(SECOND),
        "result": result,
        "variables": len(all_triples),
        "clauses": len(clauses),
        "base_clause_counts": counts,
        "fixed_strong_clauses": fixed_strong,
        "no_strong_seven_clauses": no_strong_seven,
        "cnf_sha256": digest,
        "model": str(model_path) if result == "SAT" else None,
        "model_sha256": (
            hashlib.sha256(model_path.read_bytes()).hexdigest()
            if result == "SAT" else None
        ),
        "validation": validation,
        "elapsed_seconds": round(time.monotonic() - start, 3),
        "solver_output_tail": completed.stdout[-2000:],
    }
    write_atomic(args.output.with_suffix(args.output.suffix + ".json"),
                 json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, sort_keys=True))
    raise SystemExit(10 if result == "SAT" else 20 if result == "UNSAT" else 1)


if __name__ == "__main__":
    main()
