#!/usr/bin/env python3
"""Bounded falsifier for the noncircular k=9 extreme-exchange proposal.

This searches abstract rank-three signotopes only.  SAT is computational
evidence against the proposed extraction lemma; UNSAT is not a Lean theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import time
from pathlib import Path


N = 17
TRIPLES = tuple(itertools.combinations(range(N), 3))
QUADS = tuple(itertools.combinations(range(N), 4))
TRIPLE_VAR = {triple: index + 1 for index, triple in enumerate(TRIPLES)}


def forbidden(keys, values):
    return [-TRIPLE_VAR[key] if value else TRIPLE_VAR[key]
            for key, value in zip(keys, values)]


def orientation_data(tag: str):
    if tag == "8-9":
        return tuple(range(8)), tuple(range(8, 17)), 16, tuple(range(8, 16))
    if tag == "9-8":
        return tuple(range(9, 17)), tuple(range(9)), 0, tuple(range(1, 9))
    raise ValueError(tag)


def build_formula(tag: str):
    small, big, q, core = orientation_data(tag)
    clauses: list[list[int]] = []
    counts = {"signotope": 0, "equality_definition": 0, "no_cap_four": 0,
              "no_strong_ten": 0, "cup_block_units": 0,
              "forbidden_exchange_cups": 0}

    for vertices in QUADS:
        a, b, c, d = vertices
        local = ((a, b, c), (a, b, d), (a, c, d), (b, c, d))
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                clauses.append(forbidden(local, values))
                counts["signotope"] += 1

    equality_var = {}
    next_var = len(TRIPLES) + 1
    for vertices in QUADS:
        a, b, c, d = vertices
        pairs = (((a, b, c), (a, b, d)), ((a, c, d), (b, c, d)))
        for side, (left, right) in enumerate(pairs):
            equality_var[vertices, side] = next_var
            x, y, e = TRIPLE_VAR[left], TRIPLE_VAR[right], next_var
            clauses.extend(([-e, -x, y], [-e, x, -y], [e, x, y], [e, -x, -y]))
            counts["equality_definition"] += 4
            next_var += 1

    for vertices in itertools.combinations(range(N), 4):
        clauses.append([TRIPLE_VAR[triple] for triple in itertools.combinations(vertices, 3)])
        counts["no_cap_four"] += 1

    for vertices in itertools.combinations(range(N), 10):
        clause = []
        for quad in itertools.combinations(vertices, 4):
            clause.extend((-equality_var[quad, 0], -equality_var[quad, 1]))
        clauses.append(clause)
        counts["no_strong_ten"] += 1

    for block in (small, big):
        for triple in itertools.combinations(block, 3):
            clauses.append([TRIPLE_VAR[triple]])
            counts["cup_block_units"] += 1

    for p in small:
        candidate = tuple(sorted((*core, p)))
        clauses.append([-TRIPLE_VAR[triple]
                        for triple in itertools.combinations(candidate, 3)])
        counts["forbidden_exchange_cups"] += 1

    metadata = {"small": small, "big": big, "q": q, "core": core,
                "variables": next_var - 1, "counts": counts}
    return clauses, metadata


def write_cnf(path: Path, variables: int, clauses):
    text = f"p cnf {variables} {len(clauses)}\n" + "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in clauses)
    path.write_text(text)
    return hashlib.sha256(text.encode()).hexdigest()


def parse_model(output: str, variables: int):
    values = {}
    for line in output.splitlines():
        if not line.startswith("v "):
            continue
        for field in line.split()[1:]:
            literal = int(field)
            if literal:
                values[abs(literal)] = literal > 0
    if len(values) < variables:
        raise RuntimeError(f"solver model has {len(values)} of {variables} variables")
    return values


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path,
                        default=Path("/tmp/cadical-local/usr/bin/cadical"))
    parser.add_argument("--output", type=Path,
                        default=Path("runs/agents/20260811-wave3/extreme-exchange"))
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    if not args.solver.is_file():
        parser.error(f"solver not found: {args.solver}")
    args.output.mkdir(parents=True, exist_ok=True)

    results = []
    for tag in ("8-9", "9-8"):
        clauses, metadata = build_formula(tag)
        cnf_path = args.output / f"extreme-exchange-{tag}.cnf"
        proof_path = args.output / f"extreme-exchange-{tag}.lrat"
        cnf_sha = write_cnf(cnf_path, metadata["variables"], clauses)
        started = time.monotonic()
        completed = subprocess.run(
            [str(args.solver), "-q", "--seed=0", "--lrat", "--no-binary",
             "-t", str(args.timeout), str(cnf_path), str(proof_path)],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=args.timeout + 10, check=False)
        elapsed = time.monotonic() - started
        if completed.returncode == 10:
            status = "SAT"
            values = parse_model(completed.stdout, metadata["variables"])
            triple_bits = "".join("1" if values[index] else "0"
                                  for index in range(1, len(TRIPLES) + 1))
        elif completed.returncode == 20:
            status, triple_bits = "UNSAT", None
        else:
            status, triple_bits = "UNKNOWN", None
        result = {"tag": tag, "status": status, "elapsed_seconds": elapsed,
                  "cnf": str(cnf_path), "cnf_sha256": cnf_sha,
                  "clauses": len(clauses), **metadata,
                  "lrat": str(proof_path) if status == "UNSAT" else None,
                  "lrat_sha256": (hashlib.sha256(proof_path.read_bytes()).hexdigest()
                                  if status == "UNSAT" else None),
                  "lrat_bytes": proof_path.stat().st_size if status == "UNSAT" else None,
                  "triple_bits_lexicographic": triple_bits,
                  "solver_output_tail": completed.stdout[-2000:]}
        (args.output / f"result-{tag}.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n")
        results.append(result)
    summary = {"schema_version": 1,
               "model_tier": "abstract_rank_three_signotope",
               "claim_level": "computational_evidence", "results": results}
    (args.output / "result.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({r["tag"]: r["status"] for r in results}, sort_keys=True))


if __name__ == "__main__":
    main()
