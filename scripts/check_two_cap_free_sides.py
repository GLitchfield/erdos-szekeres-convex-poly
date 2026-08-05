#!/usr/bin/env python3
"""Falsify a two-cap-free-sides signotope contract by lazy SAT.

True DIMACS variables denote left turns.  The base instance imposes the
rank-three one-change law, forbids a cap on either side of a fixed cut, and
forbids ambient caps and cups of requested sizes.  Strong-polygon blockers
are separated lazily: after each SAT model, every strong subset in that model
is blocked by its exact triple-color pattern.

This is a deterministic falsification aid, not a proof producer.  SAT returns
a compact assignment that the independent checker mode validates directly.
UNSAT is only computational evidence unless its consequence is proved in
Lean (or a separately checked proof certificate is promoted).
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
    git_revision,
    strong_patterns,
    triples,
    write_atomic,
)


def base_instance(n: int, cut: int, side_cap: int, cap: int, cup: int):
    all_triples = triples(range(n))
    variables = {triple: index + 1 for index, triple in enumerate(all_triples)}
    clauses: list[list[int]] = []
    counts = {"signotope": 0, "side_cap": 0, "no_cap": 0, "no_cup": 0}

    for vertices in itertools.combinations(range(n), 4):
        i, j, k, l = vertices
        keys = ((i, j, k), (i, j, l), (i, k, l), (j, k, l))
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                clauses.append(forbidden_assignment(keys, values, variables))
                counts["signotope"] += 1

    for side in (range(cut), range(cut, n)):
        for vertices in itertools.combinations(side, side_cap):
            clauses.append([variables[key] for key in triples(vertices)])
            counts["side_cap"] += 1

    for vertices in itertools.combinations(range(n), cap):
        clauses.append([variables[key] for key in triples(vertices)])
        counts["no_cap"] += 1

    for vertices in itertools.combinations(range(n), cup):
        clauses.append([-variables[key] for key in triples(vertices)])
        counts["no_cup"] += 1

    return all_triples, variables, clauses, counts


def is_strong(vertices: tuple[int, ...], model: set[int], variables) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if ((variables[i, j, k] in model) !=
                (variables[i, j, l] in model)):
            return False
        if ((variables[i, k, l] in model) !=
                (variables[j, k, l] in model)):
            return False
    return True


def strong_blockers(n: int, size: int, model: set[int], variables,
                    all_patterns: bool):
    blockers: list[tuple[int, ...]] = []
    witnesses: list[tuple[int, ...]] = []
    patterns = strong_patterns(size) if all_patterns else ()
    for vertices in itertools.combinations(range(n), size):
        if is_strong(vertices, model, variables):
            keys = triples(vertices)
            if all_patterns:
                blockers.extend(tuple(forbidden_assignment(keys, values, variables))
                                for values in patterns)
            else:
                values = tuple(variables[key] in model for key in keys)
                blockers.append(
                    tuple(forbidden_assignment(keys, values, variables)))
            witnesses.append(vertices)
    return blockers, witnesses


def write_cnf(path: Path, variables: int, base, blockers) -> str:
    lines = [f"p cnf {variables} {len(base) + len(blockers)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in base)
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in blockers)
    content = "\n".join(lines) + "\n"
    write_atomic(path, content)
    return hashlib.sha256(content.encode()).hexdigest()


def parse_model(path: Path, variable_count: int) -> set[int]:
    tokens: list[str] = []
    for line in path.read_text().splitlines():
        if line.startswith("v "):
            tokens.extend(line.split()[1:])
    assignment = {abs(int(token)): int(token) > 0 for token in tokens
                  if int(token) != 0}
    missing = [index for index in range(1, variable_count + 1)
               if index not in assignment]
    if missing:
        raise RuntimeError(f"solver model omits {len(missing)} variables")
    return {index for index, value in assignment.items()
            if index <= variable_count and value}


def validate_assignment(n: int, cut: int, side_cap: int, cap: int, cup: int,
                        strong: int, model: set[int], variables,
                        omit_strong: bool) -> dict[str, object]:
    failures: dict[str, object] = {}
    bad_quads = []
    for vertices in itertools.combinations(range(n), 4):
        i, j, k, l = vertices
        values = [variables[key] in model for key in
                  ((i, j, k), (i, j, l), (i, k, l), (j, k, l))]
        if sum(x != y for x, y in zip(values, values[1:])) > 1:
            bad_quads.append(vertices)
    if bad_quads:
        failures["signotope"] = bad_quads[:10]

    for label, vertices_range in (("left_side_cap", range(cut)),
                                  ("right_side_cap", range(cut, n))):
        bad = [vertices for vertices in
               itertools.combinations(vertices_range, side_cap)
               if all(variables[key] not in model for key in triples(vertices))]
        if bad:
            failures[label] = bad[:10]

    bad_cap = [vertices for vertices in itertools.combinations(range(n), cap)
               if all(variables[key] not in model for key in triples(vertices))]
    if bad_cap:
        failures["ambient_cap"] = bad_cap[:10]
    bad_cup = [vertices for vertices in itertools.combinations(range(n), cup)
               if all(variables[key] in model for key in triples(vertices))]
    if bad_cup:
        failures["ambient_cup"] = bad_cup[:10]
    if not omit_strong:
        bad_strong = [vertices for vertices in
                      itertools.combinations(range(n), strong)
                      if is_strong(vertices, model, variables)]
        if bad_strong:
            failures["strong"] = bad_strong[:10]
    return {"valid": not failures, "failures": failures}


def solve(args: argparse.Namespace) -> None:
    start = time.monotonic()
    all_triples, variables, base, counts = base_instance(
        args.n, args.cut, args.side_cap, args.cap, args.cup)
    blockers: list[tuple[int, ...]] = []
    blocker_set: set[tuple[int, ...]] = set()
    history = []
    result = "LIMIT"
    final_model: set[int] | None = None
    final_witnesses: list[tuple[int, ...]] = []
    cnf_sha256 = ""
    incremental_solver = None
    if args.incremental:
        try:
            import pycryptosat
        except ImportError as error:
            raise RuntimeError(
                "--incremental requires the pycryptosat Python module") from error
        incremental_solver = pycryptosat.Solver(verbose=0, threads=1)
        for clause in base:
            incremental_solver.add_clause(clause)

    for iteration in range(args.max_rounds + 1):
        elapsed = time.monotonic() - start
        remaining = args.timeout - elapsed
        if remaining <= 0:
            break
        if incremental_solver is not None:
            sat, solution = incremental_solver.solve(time_limit=remaining)
            history_entry = {
                "iteration": iteration,
                "blockers": len(blockers),
                "solver_result": sat,
                "elapsed_seconds": round(time.monotonic() - start, 3),
            }
            if sat is False:
                result = "UNSAT"
                history.append(history_entry)
                break
            if sat is not True or solution is None:
                history.append(history_entry)
                break
            model = {index for index in range(1, len(all_triples) + 1)
                     if solution[index]}
        else:
            cnf_sha256 = write_cnf(args.output, len(all_triples), base, blockers)
            model_path = args.output.with_suffix(args.output.suffix + ".model")
            completed = subprocess.run(
                [str(args.solver), "-q", "--seed=0", "-t",
                 str(max(1, int(remaining))), "-w", str(model_path),
                 str(args.output)],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=remaining + 5)
            history_entry = {
                "iteration": iteration,
                "blockers": len(blockers),
                "solver_returncode": completed.returncode,
                "elapsed_seconds": round(time.monotonic() - start, 3),
            }
            if completed.returncode == 20:
                result = "UNSAT"
                history.append(history_entry)
                break
            if completed.returncode != 10:
                history_entry["solver_output_tail"] = completed.stdout[-2000:]
                history.append(history_entry)
                break
            model = parse_model(model_path, len(all_triples))
        if args.omit_strong:
            result = "SAT"
            final_model = model
            history.append(history_entry)
            break
        new_blockers, witnesses = strong_blockers(
            args.n, args.strong, model, variables, args.all_strong_patterns)
        fresh = [blocker for blocker in new_blockers if blocker not in blocker_set]
        history_entry["strong_witnesses"] = len(witnesses)
        history_entry["fresh_blockers"] = len(fresh)
        history.append(history_entry)
        if not witnesses:
            result = "SAT"
            final_model = model
            break
        if not fresh:
            raise RuntimeError("separation stalled on already-blocked strong patterns")
        blockers.extend(fresh)
        blocker_set.update(fresh)
        if incremental_solver is not None:
            for blocker in fresh:
                incremental_solver.add_clause(blocker)
        final_witnesses = witnesses[:10]

    if incremental_solver is not None:
        cnf_sha256 = write_cnf(args.output, len(all_triples), base, blockers)

    validation = None
    model_json = None
    if final_model is not None:
        validation = validate_assignment(
            args.n, args.cut, args.side_cap, args.cap, args.cup, args.strong,
            final_model, variables, args.omit_strong)
        if not validation["valid"]:
            raise RuntimeError(f"independent model validation failed: {validation}")
        model_json = args.output.with_suffix(args.output.suffix + ".model.json")
        write_atomic(model_json, json.dumps({
            "schema_version": 1,
            "n": args.n,
            "cut": args.cut,
            "left_triples": [list(all_triples[index - 1])
                             for index in sorted(final_model)],
            "validation": validation,
        }, indent=2, sort_keys=True) + "\n")

    manifest = {
        "schema_version": 1,
        "generator": "scripts/check_two_cap_free_sides.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "parameters": {key: getattr(args, key) for key in
                       ("n", "cut", "side_cap", "cap", "cup", "strong",
                        "omit_strong", "all_strong_patterns", "max_rounds",
                        "timeout")},
        "solver": ("pycryptosat" if args.incremental else str(args.solver)),
        "result": result,
        "variables": len(all_triples),
        "base_clauses": len(base),
        "base_clause_counts": counts,
        "lazy_strong_blockers": len(blockers),
        "last_strong_witnesses": [list(x) for x in final_witnesses],
        "history": history,
        "elapsed_seconds": round(time.monotonic() - start, 3),
        "cnf": str(args.output),
        "cnf_sha256": cnf_sha256,
        "model_json": str(model_json) if model_json else None,
        "validation": validation,
    }
    write_atomic(args.output.with_suffix(args.output.suffix + ".json"),
                 json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"result": result, "iterations": len(history),
                      "blockers": len(blockers),
                      "elapsed_seconds": manifest["elapsed_seconds"]}))
    if result == "SAT":
        raise SystemExit(10)
    if result == "UNSAT":
        raise SystemExit(20)
    raise SystemExit(1)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--cut", type=int, required=True)
    parser.add_argument("--side-cap", type=int, default=4)
    parser.add_argument("--cap", type=int, default=5)
    parser.add_argument("--cup", type=int, default=6)
    parser.add_argument("--strong", type=int, default=7)
    parser.add_argument("--omit-strong", action="store_true")
    parser.add_argument("--all-strong-patterns", action="store_true",
                        help="block every strong pattern on each witnessed subset")
    parser.add_argument("--max-rounds", type=int, default=100)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--solver", type=Path,
                        default=Path("/tmp/cadical-local/usr/bin/cadical"))
    parser.add_argument("--incremental", action="store_true",
                        help="reuse learned clauses through pycryptosat")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 0 < args.cut < args.n:
        parser.error("cut must lie strictly between zero and n")
    if min(args.side_cap, args.cap, args.cup, args.strong) < 3:
        parser.error("all forbidden sizes must be at least three")
    if max(args.side_cap, args.cap, args.cup, args.strong) > args.n:
        parser.error("forbidden sizes cannot exceed n")
    if args.timeout <= 0 or args.max_rounds < 0:
        parser.error("timeout must be positive and max-rounds nonnegative")
    if not args.incremental and not args.solver.is_file():
        parser.error(f"solver does not exist: {args.solver}")
    solve(args)


if __name__ == "__main__":
    main()
