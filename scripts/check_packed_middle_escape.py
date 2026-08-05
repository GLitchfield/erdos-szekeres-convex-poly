#!/usr/bin/env python3
"""Falsify the packed middle-split escape contract on a balanced cut.

The instance imposes the parent one-change and avoidance laws, forbids an
internal strong six on either side, and requires every six-set deletion to
leave a strong six.  Its route negation selects one deletion for which no
disjoint extreme (1+5 or 5+1) strong six exists.  Packing then guarantees a
disjoint middle-split witness for the selected deletion.

SAT is a countermodel candidate checked by a separate direct verifier.  UNSAT
is route-selection evidence only and is not a Lean proof.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import time
from pathlib import Path

from check_two_cap_free_sides import base_instance, parse_model, write_cnf
from generate_signotope_state_sat import git_revision, write_atomic


def comparison_key(left, right):
    return (left, right) if left < right else (right, left)


def strong_comparisons(vertices):
    result = []
    for middle_index in range(1, len(vertices) - 1):
        middle = vertices[middle_index]
        centered = [
            (left, middle, right)
            for left in vertices[:middle_index]
            for right in vertices[middle_index + 1:]
        ]
        anchor = centered[0]
        result.extend(comparison_key(anchor, other) for other in centered[1:])
    return tuple(dict.fromkeys(result))


def add_xor_definition(clauses, difference, left, right) -> None:
    clauses.extend((
        [-left, -right, -difference],
        [left, right, -difference],
        [left, -right, difference],
        [-left, right, difference],
    ))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=16)
    parser.add_argument("--cut", type=int, default=8)
    parser.add_argument(
        "--mode", choices=("base", "counterexample"), default="counterexample"
    )
    parser.add_argument(
        "--deleted",
        help="comma-separated fixed deleted six-set; omitting it lets SAT select one",
    )
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument(
        "--packing-mode", choices=("eager", "lazy"), default="eager"
    )
    parser.add_argument("--packing-batch", type=int, default=256)
    parser.add_argument("--max-rounds", type=int, default=32)
    parser.add_argument(
        "--solver", type=Path, default=Path("/tmp/cadical-local/usr/bin/cadical")
    )
    args = parser.parse_args()
    if args.n < 12 or abs(args.cut * 2 - args.n) > 1:
        parser.error(
            "this gate requires a balanced or near-balanced cut with at least 12 vertices"
        )
    if not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")
    if args.packing_batch <= 0 or args.max_rounds < 0:
        parser.error("packing batch must be positive and max rounds nonnegative")
    fixed_deleted = None
    if args.deleted:
        try:
            fixed_deleted = tuple(sorted(int(item) for item in args.deleted.split(",")))
        except ValueError:
            parser.error("--deleted must be a comma-separated integer list")
        if len(fixed_deleted) != 6 or len(set(fixed_deleted)) != 6:
            parser.error("--deleted must contain exactly six distinct vertices")
        if fixed_deleted[0] < 0 or fixed_deleted[-1] >= args.n:
            parser.error("--deleted contains a vertex outside the instance")
        if args.mode != "counterexample":
            parser.error("--deleted is meaningful only in counterexample mode")

    start = time.monotonic()
    all_triples, triple_vars, clauses, counts = base_instance(
        args.n, args.cut, 4, 5, 6
    )
    sixes = tuple(itertools.combinations(range(args.n), 6))
    sevens = tuple(itertools.combinations(range(args.n), 7))
    next_var = len(all_triples) + 1

    all_comparisons = {}
    six_comparisons = {}
    for vertices in sixes:
        comparisons = strong_comparisons(vertices)
        six_comparisons[vertices] = comparisons
        for comparison in comparisons:
            if comparison not in all_comparisons:
                all_comparisons[comparison] = next_var
                next_var += 1
    seven_comparisons = {}
    for vertices in sevens:
        comparisons = strong_comparisons(vertices)
        seven_comparisons[vertices] = comparisons
        for comparison in comparisons:
            if comparison not in all_comparisons:
                all_comparisons[comparison] = next_var
                next_var += 1
    for (left, right), difference in all_comparisons.items():
        add_xor_definition(
            clauses, difference, triple_vars[left], triple_vars[right]
        )
    counts["xor_definitions"] = 4 * len(all_comparisons)

    strong_vars = {}
    for vertices in sixes:
        strong_var = next_var
        next_var += 1
        strong_vars[vertices] = strong_var
        differences = [all_comparisons[item] for item in six_comparisons[vertices]]
        clauses.extend([-strong_var, -difference] for difference in differences)
        clauses.append([strong_var, *differences])
    counts["strong_six_definitions"] = sum(
        len(six_comparisons[vertices]) + 1 for vertices in sixes
    )

    counts["no_internal_strong_six"] = 0
    for vertices, strong_var in strong_vars.items():
        left_count = sum(vertex < args.cut for vertex in vertices)
        if left_count in (0, 6):
            clauses.append([-strong_var])
            counts["no_internal_strong_six"] += 1

    counts["no_strong_seven"] = 0
    for vertices in sevens:
        clauses.append([
            all_comparisons[comparison]
            for comparison in seven_comparisons[vertices]
        ])
        counts["no_strong_seven"] += 1

    counts["packing"] = 0
    six_masks = {
        vertices: sum(1 << vertex for vertex in vertices) for vertices in sixes
    }
    deletion_masks = dict(six_masks)

    def packing_clause(deleted):
        deleted_mask = deletion_masks[deleted]
        result = [
            strong_vars[vertices] for vertices in sixes
            if not (six_masks[vertices] & deleted_mask)
        ]
        if not result:
            raise RuntimeError(f"deletion {deleted} has no six-set complement witness")
        return result

    packed_deletions = set()
    if args.packing_mode == "eager":
        for deleted in sixes:
            clauses.append(packing_clause(deleted))
            packed_deletions.add(deleted)
        counts["packing"] = len(packed_deletions)

    deletion_vars = {}
    if args.mode == "counterexample" and fixed_deleted is None:
        for deleted in sixes:
            deletion_vars[deleted] = next_var
            next_var += 1
        clauses.append(list(deletion_vars.values()))
    counts["select_bad_deletion"] = int(bool(deletion_vars))
    counts["selected_deletion_no_extreme"] = 0
    selected_targets = (
        ((fixed_deleted, None),) if fixed_deleted is not None
        else tuple(deletion_vars.items())
    )
    for deleted, selected in selected_targets:
        deleted_mask = deletion_masks[deleted]
        for vertices, strong_var in strong_vars.items():
            left_count = sum(vertex < args.cut for vertex in vertices)
            if left_count in (1, 5) and not (six_masks[vertices] & deleted_mask):
                clauses.append(
                    [-strong_var] if selected is None else [-selected, -strong_var]
                )
                counts["selected_deletion_no_extreme"] += 1

    variable_count = next_var - 1
    model_path = args.output.with_suffix(args.output.suffix + ".model")
    digest = ""
    completed = None
    model = None
    history = []
    result = "LIMIT"
    for iteration in range(args.max_rounds + 1):
        remaining = args.timeout - (time.monotonic() - start)
        if remaining <= 1:
            break
        digest = write_cnf(args.output, variable_count, clauses, ())
        completed = subprocess.run(
            [
                str(args.solver), "-q", "--seed=0", "-t",
                str(max(1, int(remaining))), "-w", str(model_path),
                str(args.output),
            ],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=remaining + 5,
        )
        status = {10: "SAT", 20: "UNSAT"}.get(completed.returncode, "LIMIT")
        round_record = {
            "iteration": iteration,
            "status": status,
            "packing_clauses": len(packed_deletions),
            "elapsed_seconds": round(time.monotonic() - start, 3),
        }
        history.append(round_record)
        if status != "SAT":
            result = status
            break
        model = parse_model(model_path, variable_count)
        if args.packing_mode == "eager":
            result = "SAT"
            break
        true_strong_masks = [
            six_masks[vertices] for vertices, variable in strong_vars.items()
            if variable in model
        ]
        uncovered = [
            deleted for deleted in sixes
            if not any(
                deletion_masks[deleted] & witness == 0
                for witness in true_strong_masks
            )
        ]
        round_record["uncovered_deletions"] = len(uncovered)
        if not uncovered:
            result = "SAT"
            break
        if iteration == args.max_rounds:
            break
        fresh = [item for item in uncovered if item not in packed_deletions]
        if not fresh:
            raise RuntimeError("lazy packing stalled on already imposed deletions")
        for deleted in fresh[:args.packing_batch]:
            clauses.append(packing_clause(deleted))
            packed_deletions.add(deleted)
        counts["packing"] = len(packed_deletions)

    model_json = None
    model_sha256 = None
    if result == "SAT":
        assert model is not None
        selected = (
            [list(fixed_deleted)] if fixed_deleted is not None else [
                list(vertices) for vertices, variable in deletion_vars.items()
                if variable in model
            ]
        )
        true_triples = [
            list(triple) for triple, variable in triple_vars.items() if variable in model
        ]
        model_json = args.output.with_suffix(args.output.suffix + ".model.json")
        write_atomic(model_json, json.dumps({
            "schema_version": 1,
            "n": args.n,
            "cut": args.cut,
            "mode": args.mode,
            "left_triples": true_triples,
            "selected_deletions": selected,
        }, indent=2, sort_keys=True) + "\n")
        model_sha256 = hashlib.sha256(model_json.read_bytes()).hexdigest()

    manifest = {
        "schema_version": 1,
        "generator": "scripts/check_packed_middle_escape.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "parameters": {
            "n": args.n,
            "cut": args.cut,
            "mode": args.mode,
            "deleted": list(fixed_deleted) if fixed_deleted is not None else None,
            "packing_mode": args.packing_mode,
            "packing_batch": args.packing_batch,
            "max_rounds": args.max_rounds,
            "timeout": args.timeout,
        },
        "result": result,
        "variables": variable_count,
        "clauses": len(clauses),
        "clause_counts": counts,
        "cnf": str(args.output),
        "cnf_sha256": digest,
        "model_json": str(model_json) if model_json else None,
        "model_sha256": model_sha256,
        "history": history,
        "elapsed_seconds": round(time.monotonic() - start, 3),
        "solver_output_tail": completed.stdout[-2000:] if completed else "",
        "evidence_ceiling": "SAT falsifies the abstract contract after replay; UNSAT is not a Lean proof",
    }
    write_atomic(
        args.output.with_suffix(args.output.suffix + ".json"),
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
    )
    print(json.dumps(manifest, sort_keys=True))
    raise SystemExit(10 if result == "SAT" else 20 if result == "UNSAT" else 1)


if __name__ == "__main__":
    main()
