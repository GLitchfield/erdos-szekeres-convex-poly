#!/usr/bin/env python3
"""Falsify multiplicity bounds for a fixed balanced-branch residue.

The external vertices precede one fixed residue.  Each external vertex must
form either a cap four with a common three-residue or a strong six with a
common five-residue.  Both blocks are four-cap-free, and the ambient coloring
avoids a cap five, cup six, and strong seven whenever those sizes exist.

This is a deterministic route-selection experiment, not a proof producer.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import time
from pathlib import Path

from generate_signotope_state_sat import (
    forbidden_assignment,
    strong_patterns,
    triples,
    write_atomic,
)


def add_equality(clauses, left, right):
    clauses.extend(([-left, right], [left, -right]))


def is_strong(vertices, true_variables, variables):
    for i, j, k, l in itertools.combinations(vertices, 4):
        if ((variables[i, j, k] in true_variables) !=
                (variables[i, j, l] in true_variables)):
            return False
        if ((variables[i, k, l] in true_variables) !=
                (variables[j, k, l] in true_variables)):
            return False
    return True


def build(case, external_count, side_count, no_side_strong_six):
    residue_count = 3 if case == "cap" else 5
    n = external_count + side_count
    external = tuple(range(external_count))
    side = tuple(range(external_count, n))
    residue = side[:residue_count]
    all_triples = triples(range(n))
    variables = {triple: index + 1 for index, triple in enumerate(all_triples)}
    clauses = []
    counts = {
        "one_change": 0,
        "no_cap_five": 0,
        "no_cup_six": 0,
        "no_strong_seven": 0,
        "side_cap_four": 0,
        "no_side_strong_six": 0,
        "fixed_residue": 0,
    }

    for vertices in itertools.combinations(range(n), 4):
        i, j, k, l = vertices
        keys = ((i, j, k), (i, j, l), (i, k, l), (j, k, l))
        for values in itertools.product((False, True), repeat=4):
            if sum(a != b for a, b in zip(values, values[1:])) > 1:
                clauses.append(forbidden_assignment(keys, values, variables))
                counts["one_change"] += 1

    for vertices in itertools.combinations(range(n), 5):
        clauses.append([variables[key] for key in triples(vertices)])
        counts["no_cap_five"] += 1
    for vertices in itertools.combinations(range(n), 6):
        clauses.append([-variables[key] for key in triples(vertices)])
        counts["no_cup_six"] += 1
    patterns = strong_patterns(7) if n >= 7 else ()
    local = triples(range(7))
    for vertices in itertools.combinations(range(n), 7):
        keys = tuple(tuple(vertices[index] for index in triple)
                     for triple in local)
        for values in patterns:
            clauses.append(forbidden_assignment(keys, values, variables))
            counts["no_strong_seven"] += 1

    for block in (external, side):
        for vertices in itertools.combinations(block, 4):
            clauses.append([variables[key] for key in triples(vertices)])
            counts["side_cap_four"] += 1
    if no_side_strong_six:
        local_six = triples(range(6))
        for vertices in itertools.combinations(side, 6):
            keys = tuple(tuple(vertices[index] for index in triple)
                         for triple in local_six)
            for values in strong_patterns(6):
                clauses.append(forbidden_assignment(keys, values, variables))
                counts["no_side_strong_six"] += 1

    for q in external:
        witness = tuple(sorted((q, *residue)))
        if case == "cap":
            for key in triples(witness):
                clauses.append([-variables[key]])
                counts["fixed_residue"] += 1
        else:
            for i, j, k, l in itertools.combinations(witness, 4):
                add_equality(clauses, variables[i, j, k], variables[i, j, l])
                add_equality(clauses, variables[i, k, l], variables[j, k, l])
                counts["fixed_residue"] += 4
    return n, external, side, residue, all_triples, variables, clauses, counts


def parse_model(path, variable_count):
    tokens = []
    for line in path.read_text().splitlines():
        if line.startswith("v "):
            tokens.extend(line.split()[1:])
    assignment = {abs(int(token)): int(token) > 0 for token in tokens
                  if int(token)}
    if any(index not in assignment for index in range(1, variable_count + 1)):
        raise RuntimeError("solver returned an incomplete assignment")
    return {index for index, value in assignment.items() if value}


def validate(case, n, external, side, residue, true_variables, variables,
             no_side_strong_six):
    for i, j, k, l in itertools.combinations(range(n), 4):
        values = [variables[key] in true_variables for key in
                  ((i, j, k), (i, j, l), (i, k, l), (j, k, l))]
        if sum(a != b for a, b in zip(values, values[1:])) > 1:
            raise RuntimeError(f"one-change failure on {(i, j, k, l)}")
    for block in (external, side):
        for vertices in itertools.combinations(block, 4):
            if all(variables[key] not in true_variables
                   for key in triples(vertices)):
                raise RuntimeError(f"side cap four on {vertices}")
    for size, color, label in ((5, False, "cap"), (6, True, "cup")):
        for vertices in itertools.combinations(range(n), size):
            if all((variables[key] in true_variables) == color
                   for key in triples(vertices)):
                raise RuntimeError(f"ambient {label} on {vertices}")
    for vertices in itertools.combinations(range(n), 7):
        if is_strong(vertices, true_variables, variables):
            raise RuntimeError(f"ambient strong seven on {vertices}")
    if no_side_strong_six:
        for vertices in itertools.combinations(side, 6):
            if is_strong(vertices, true_variables, variables):
                raise RuntimeError(f"side strong six on {vertices}")
    for q in external:
        witness = tuple(sorted((q, *residue)))
        if case == "cap":
            if any(variables[key] in true_variables for key in triples(witness)):
                raise RuntimeError(f"fixed cap residue fails at {q}")
        elif not is_strong(witness, true_variables, variables):
            raise RuntimeError(f"fixed strong residue fails at {q}")


def write_cnf(path, variable_count, clauses):
    content = f"p cnf {variable_count} {len(clauses)}\n"
    content += "".join(" ".join(map(str, clause)) + " 0\n"
                       for clause in clauses)
    write_atomic(path, content)
    return hashlib.sha256(content.encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=("cap", "strong"), required=True)
    parser.add_argument("--max-external", type=int, default=6)
    parser.add_argument("--side-size", type=int)
    parser.add_argument("--no-side-strong-six", action="store_true")
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--solver", type=Path,
                        default=Path("/tmp/cadical-local/usr/bin/cadical"))
    args = parser.parse_args()
    if not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")
    if args.max_external < 2:
        parser.error("max-external must be at least two")
    residue_count = 3 if args.case == "cap" else 5
    side_count = args.side_size if args.side_size is not None else residue_count
    if side_count < residue_count:
        parser.error("side-size is smaller than the requested residue")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    records = []
    start = time.monotonic()
    for external_count in range(2, args.max_external + 1):
        built = build(args.case, external_count, side_count,
                      args.no_side_strong_six)
        n, external, side, residue, all_triples, variables, clauses, counts = built
        cnf = args.output_dir / f"{args.case}-{external_count}.cnf"
        digest = write_cnf(cnf, len(all_triples), clauses)
        model = cnf.with_suffix(".model")
        completed = subprocess.run(
            [str(args.solver), "-q", "--seed=0", "-t", str(args.timeout),
             "-w", str(model), str(cnf)],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=args.timeout + 5,
        )
        result = {10: "SAT", 20: "UNSAT"}.get(completed.returncode, "LIMIT")
        model_digest = None
        validated = False
        if result == "SAT":
            true_variables = parse_model(model, len(all_triples))
            validate(args.case, n, external, side, residue, true_variables,
                     variables, args.no_side_strong_six)
            model_digest = hashlib.sha256(model.read_bytes()).hexdigest()
            validated = True
        records.append({
            "external_count": external_count,
            "side_count": side_count,
            "n": n,
            "result": result,
            "variables": len(all_triples),
            "clauses": len(clauses),
            "clause_counts": counts,
            "cnf_sha256": digest,
            "model_sha256": model_digest,
            "validated": validated,
        })
    summary = {
        "schema_version": 1,
        "generator": "scripts/check_repeated_residue_fibers.py",
        "case": args.case,
        "max_external": args.max_external,
        "side_count": side_count,
        "no_side_strong_six": args.no_side_strong_six,
        "records": records,
        "elapsed_seconds": round(time.monotonic() - start, 3),
    }
    write_atomic(args.output_dir / "summary.json",
                 json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
