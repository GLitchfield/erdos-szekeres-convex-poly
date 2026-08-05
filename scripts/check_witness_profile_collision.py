#!/usr/bin/env python3
"""Test a two-vertex witness-profile collision under the residual exclusions.

The fixed witness is either a cap or a strong polygon.  Two vertices in the
same order gap are constrained to have identical colors with every pair of
witness vertices.  A SAT result is an independently checked counterexample to
the corresponding naive collision claim; UNSAT remains computational evidence.
"""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
from pathlib import Path

from check_two_cap_free_sides import (
    base_instance,
    is_strong,
    parse_model,
    validate_assignment,
    write_cnf,
)
from generate_signotope_state_sat import (
    forbidden_assignment,
    git_revision,
    strong_patterns,
    triples,
    write_atomic,
)


def sorted_triple(a: int, b: int, c: int) -> tuple[int, int, int]:
    return tuple(sorted((a, b, c)))


def parse_vertices(value: str) -> tuple[int, ...]:
    try:
        result = tuple(int(item) for item in value.split(","))
    except ValueError as error:
        raise argparse.ArgumentTypeError("vertices must be comma-separated integers") from error
    if len(set(result)) != len(result):
        raise argparse.ArgumentTypeError("witness vertices must be distinct")
    return tuple(sorted(result))


def add_equality(clauses: list[list[int]], left: int, right: int) -> None:
    clauses.append([-left, right])
    clauses.append([left, -right])


def solve(args: argparse.Namespace) -> None:
    all_triples, variables, clauses, counts = base_instance(
        args.n, args.cut, args.side_cap, args.cap, args.cup)
    witness = args.witness
    witness_set = set(witness)
    if args.first in witness_set or args.second in witness_set:
        raise ValueError("profile vertices must lie outside the witness")
    if not args.first < args.second:
        raise ValueError("profile vertices must be strictly ordered")
    gaps = [sum(vertex < q for vertex in witness)
            for q in (args.first, args.second)]
    if gaps[0] != gaps[1]:
        raise ValueError("profile vertices must occupy the same witness gap")

    witness_clauses = 0
    if args.kind == "cap":
        for key in triples(witness):
            clauses.append([-variables[key]])
            witness_clauses += 1
    else:
        for i, j, k, l in itertools.combinations(witness, 4):
            add_equality(clauses, variables[i, j, k], variables[i, j, l])
            add_equality(clauses, variables[i, k, l], variables[j, k, l])
            witness_clauses += 4

    profile_clauses = 0
    for a, b in itertools.combinations(witness, 2):
        left = variables[sorted_triple(args.first, a, b)]
        right = variables[sorted_triple(args.second, a, b)]
        add_equality(clauses, left, right)
        profile_clauses += 2

    strong_clauses = 0
    patterns = strong_patterns(args.strong)
    for vertices in itertools.combinations(range(args.n), args.strong):
        keys = triples(vertices)
        for values in patterns:
            clauses.append(forbidden_assignment(keys, values, variables))
            strong_clauses += 1

    sha256 = write_cnf(args.output, len(all_triples), clauses, ())
    model_path = args.output.with_suffix(args.output.suffix + ".model")
    completed = subprocess.run(
        [str(args.solver), "-q", "--seed=0", "-t", str(args.timeout),
         "-w", str(model_path), str(args.output)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=args.timeout + 5)
    result = "SAT" if completed.returncode == 10 else (
        "UNSAT" if completed.returncode == 20 else "LIMIT")
    validation = None
    model_json = None
    if result == "SAT":
        model = parse_model(model_path, len(all_triples))
        validation = validate_assignment(
            args.n, args.cut, args.side_cap, args.cap, args.cup,
            args.strong, model, variables, False)
        witness_valid = (
            all(variables[key] not in model for key in triples(witness))
            if args.kind == "cap" else is_strong(witness, model, variables))
        profile_valid = all(
            (variables[sorted_triple(args.first, a, b)] in model) ==
            (variables[sorted_triple(args.second, a, b)] in model)
            for a, b in itertools.combinations(witness, 2))
        validation["witness_valid"] = witness_valid
        validation["profile_valid"] = profile_valid
        validation["valid"] = validation["valid"] and witness_valid and profile_valid
        if not validation["valid"]:
            raise RuntimeError(f"independent validation failed: {validation}")
        model_json = args.output.with_suffix(args.output.suffix + ".model.json")
        write_atomic(model_json, json.dumps({
            "schema_version": 1,
            "n": args.n,
            "cut": args.cut,
            "kind": args.kind,
            "witness": list(witness),
            "profile_vertices": [args.first, args.second],
            "left_triples": [list(all_triples[index - 1])
                             for index in sorted(model)],
            "validation": validation,
        }, indent=2, sort_keys=True) + "\n")

    manifest = {
        "schema_version": 1,
        "generator": "scripts/check_witness_profile_collision.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "parameters": {
            "n": args.n, "cut": args.cut, "kind": args.kind,
            "witness": list(witness), "first": args.first,
            "second": args.second, "side_cap": args.side_cap,
            "cap": args.cap, "cup": args.cup, "strong": args.strong,
            "timeout": args.timeout,
        },
        "result": result,
        "variables": len(all_triples),
        "clauses": len(clauses),
        "base_clause_counts": counts,
        "witness_clauses": witness_clauses,
        "profile_clauses": profile_clauses,
        "strong_clauses": strong_clauses,
        "cnf": str(args.output),
        "cnf_sha256": sha256,
        "model_json": str(model_json) if model_json else None,
        "validation": validation,
        "solver_output_tail": completed.stdout[-2000:],
    }
    write_atomic(args.output.with_suffix(args.output.suffix + ".json"),
                 json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"result": result, "variables": len(all_triples),
                      "clauses": len(clauses), "validation": validation}))
    raise SystemExit(10 if result == "SAT" else 20 if result == "UNSAT" else 1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--cut", type=int, required=True)
    parser.add_argument("--kind", choices=("cap", "strong"), required=True)
    parser.add_argument("--witness", type=parse_vertices, required=True)
    parser.add_argument("--first", type=int, required=True)
    parser.add_argument("--second", type=int, required=True)
    parser.add_argument("--side-cap", type=int, default=4)
    parser.add_argument("--cap", type=int, default=5)
    parser.add_argument("--cup", type=int, default=6)
    parser.add_argument("--strong", type=int, default=7)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--solver", type=Path,
                        default=Path("/tmp/cadical-local/usr/bin/cadical"))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 0 < args.cut < args.n:
        parser.error("cut must lie strictly between zero and n")
    if any(not 0 <= vertex < args.n for vertex in
           (*args.witness, args.first, args.second)):
        parser.error("all vertices must lie in range(n)")
    expected = 4 if args.kind == "cap" else 6
    if len(args.witness) != expected:
        parser.error(f"{args.kind} witness must have {expected} vertices")
    if not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")
    solve(args)


if __name__ == "__main__":
    main()
