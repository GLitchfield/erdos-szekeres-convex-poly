#!/usr/bin/env python3
"""Falsify parent-relevant bridge routes for the fixed crossing `3+3` pair.

The base instance is the independently checked twelve-point obstruction from
experiment 0019. Route clauses ask whether that obstruction can additionally
avoid a common frame anchor in either direction, or avoid every extreme
`1+5`/`5+1` strong six. SAT models are evidence against the corresponding
universal claim. UNSAT is advisory unless promoted through a checked proof.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import time
from pathlib import Path

from check_middle_split_pair import (
    CUT,
    FIRST,
    N,
    SECOND,
    add_strong,
    write_cnf,
)
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


ROUTES = ("no-shared-first", "no-shared-second", "no-shared-both", "no-extreme")
FIRST_INTERIOR_PROBES = (3, 4, 5)
SECOND_INTERIOR_PROBES = (6, 7, 8)


def common_frames(reference, probes):
    result = []
    for frame in itertools.combinations(reference, 3):
        x, y, z = frame
        if all((x < q < y < z) or (x < y < q < z) for q in probes):
            result.append(frame)
    return tuple(result)


def add_no_shared_anchor(clauses, variables, reference, probes) -> int:
    before = len(clauses)
    for x, y, z in common_frames(reference, probes):
        frame = variables[x, y, z]
        probe_colors = [variables[x, q, z] for q in probes]
        clauses.append([frame, *probe_colors])
        clauses.append([-frame, *(-color for color in probe_colors)])
    return len(clauses) - before


def add_no_extreme_strong_six(clauses, variables) -> int:
    before = len(clauses)
    local = triples(range(6))
    for vertices in itertools.combinations(range(N), 6):
        left_count = sum(vertex < CUT for vertex in vertices)
        if left_count not in (1, 5):
            continue
        keys = tuple(tuple(vertices[index] for index in triple) for triple in local)
        for values in strong_patterns(6):
            clauses.append(forbidden_assignment(keys, values, variables))
    return len(clauses) - before


def shared_frames(model, variables, reference, probes):
    result = []
    for x, y, z in common_frames(reference, probes):
        frame_color = variables[x, y, z] in model
        if all((variables[x, q, z] in model) == frame_color for q in probes):
            result.append((x, y, z))
    return result


def extreme_strong_sixes(model, variables):
    return [
        vertices
        for vertices in itertools.combinations(range(N), 6)
        if sum(vertex < CUT for vertex in vertices) in (1, 5)
        and is_strong(vertices, model, variables)
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--route", required=True, choices=ROUTES)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument(
        "--solver", type=Path, default=Path("/tmp/cadical-local/usr/bin/cadical")
    )
    args = parser.parse_args()
    if not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")

    start = time.monotonic()
    all_triples, variables, clauses, counts = base_instance(N, CUT, 4, 5, 6)
    counts["fixed_strong"] = add_strong(clauses, variables, FIRST)
    counts["fixed_strong"] += add_strong(clauses, variables, SECOND)
    counts["no_strong_seven"] = 0
    local = triples(range(7))
    for vertices in itertools.combinations(range(N), 7):
        keys = tuple(tuple(vertices[index] for index in triple) for triple in local)
        for values in strong_patterns(7):
            clauses.append(forbidden_assignment(keys, values, variables))
            counts["no_strong_seven"] += 1

    counts["route"] = 0
    if args.route in ("no-shared-first", "no-shared-both"):
        counts["route"] += add_no_shared_anchor(
            clauses, variables, FIRST, FIRST_INTERIOR_PROBES
        )
    if args.route in ("no-shared-second", "no-shared-both"):
        counts["route"] += add_no_shared_anchor(
            clauses, variables, SECOND, SECOND_INTERIOR_PROBES
        )
    if args.route == "no-extreme":
        counts["route"] += add_no_extreme_strong_six(clauses, variables)

    digest = write_cnf(args.output, len(all_triples), clauses)
    model_path = args.output.with_suffix(args.output.suffix + ".model")
    completed = subprocess.run(
        [
            str(args.solver), "-q", "--seed=0", "-t", str(args.timeout),
            "-w", str(model_path), str(args.output),
        ],
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
        validation["first_shared_frames"] = shared_frames(
            model, variables, FIRST, FIRST_INTERIOR_PROBES
        )
        validation["second_shared_frames"] = shared_frames(
            model, variables, SECOND, SECOND_INTERIOR_PROBES
        )
        validation["extreme_strong_sixes"] = extreme_strong_sixes(model, variables)
        route_valid = {
            "no-shared-first": not validation["first_shared_frames"],
            "no-shared-second": not validation["second_shared_frames"],
            "no-shared-both": not validation["first_shared_frames"]
                and not validation["second_shared_frames"],
            "no-extreme": not validation["extreme_strong_sixes"],
        }[args.route]
        validation["valid"] = validation["valid"] and route_valid
        validation["valid"] = validation["valid"] and validation["first_strong"]
        validation["valid"] = validation["valid"] and validation["second_strong"]
        if not validation["valid"]:
            raise RuntimeError(f"model validation failed: {validation}")

    manifest = {
        "schema_version": 1,
        "generator": "scripts/check_middle_split_bridge_routes.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "route": args.route,
        "parameters": {
            "n": N,
            "cut": CUT,
            "first": FIRST,
            "second": SECOND,
            "timeout": args.timeout,
        },
        "result": result,
        "variables": len(all_triples),
        "clauses": len(clauses),
        "clause_counts": counts,
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
    write_atomic(
        args.output.with_suffix(args.output.suffix + ".json"),
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
    )
    print(json.dumps(manifest, sort_keys=True))
    raise SystemExit(10 if result == "SAT" else 20 if result == "UNSAT" else 1)


if __name__ == "__main__":
    main()
