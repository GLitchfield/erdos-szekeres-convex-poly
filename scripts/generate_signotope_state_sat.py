#!/usr/bin/env python3
"""Generate a CNF searching for an extremal rank-three signotope state.

Variables are increasing triples; true means a left turn.  The clauses impose
the one-change law and forbid an ``a``-cap, a ``u``-cup, and a strong
``k``-set.  This is a necessary-condition search for decomposable colorings,
because ``IsDecomposableOn.turnSequenceAllowed`` proves that every such
coloring is a signotope.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import subprocess
from pathlib import Path


def triples(vertices) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(vertices, 3))


def forbidden_assignment(keys, values, variables) -> list[int]:
    return [-variables[key] if value else variables[key]
            for key, value in zip(keys, values)]


def strong_patterns(size: int) -> tuple[tuple[bool, ...], ...]:
    local = triples(range(size))
    positions = {triple: index for index, triple in enumerate(local)}
    parent = list(range(len(local)))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        x, y = find(x), find(y)
        if x != y:
            parent[y] = x

    for i, j, k, l in itertools.combinations(range(size), 4):
        union(positions[i, j, k], positions[i, j, l])
        union(positions[i, k, l], positions[j, k, l])
    roots = sorted({find(index) for index in range(len(local))})
    component = {root: index for index, root in enumerate(roots)}
    return tuple(
        tuple(assignment[component[find(index)]] for index in range(len(local)))
        for assignment in itertools.product((False, True), repeat=len(roots))
    )


def generate(n: int, a: int, u: int, k: int):
    all_triples = triples(range(n))
    variables = {triple: index + 1 for index, triple in enumerate(all_triples)}
    clauses: list[list[int]] = []
    origins: list[tuple[str, tuple[int, ...], tuple[bool, ...]]] = []
    counts = {"signotope": 0, "no_cap": 0, "no_cup": 0, "no_strong": 0}

    for vertices in itertools.combinations(range(n), 4):
        i, j, m, l = vertices
        keys = ((i, j, m), (i, j, l), (i, m, l), (j, m, l))
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                clauses.append(forbidden_assignment(keys, values, variables))
                origins.append(("quad", vertices, values))
                counts["signotope"] += 1

    for vertices in itertools.combinations(range(n), a):
        keys = triples(vertices)
        clauses.append([variables[key] for key in keys])
        origins.append(("cap", vertices, tuple(False for _ in keys)))
        counts["no_cap"] += 1

    for vertices in itertools.combinations(range(n), u):
        keys = triples(vertices)
        clauses.append([-variables[key] for key in keys])
        origins.append(("cup", vertices, tuple(True for _ in keys)))
        counts["no_cup"] += 1

    local_triples = triples(range(k))
    patterns = strong_patterns(k)
    for vertices in itertools.combinations(range(n), k):
        keys = tuple(tuple(vertices[index] for index in triple)
                     for triple in local_triples)
        for values in patterns:
            clauses.append(forbidden_assignment(keys, values, variables))
            origins.append(("strong", vertices, values))
            counts["no_strong"] += 1
    return all_triples, clauses, origins, counts, len(patterns)


def write_atomic(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(content)
    os.replace(temporary, path)


def git_revision(repo: Path) -> str:
    result = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo, check=True, text=True, stdout=subprocess.PIPE)
    return result.stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--cap", type=int, required=True)
    parser.add_argument("--cup", type=int, required=True)
    parser.add_argument("--strong", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if min(args.cap, args.cup, args.strong) < 3:
        parser.error("cap, cup, and strong sizes must be at least three")
    if max(args.cap, args.cup, args.strong) > args.n:
        parser.error("forbidden subset sizes cannot exceed n")

    all_triples, clauses, _, counts, pattern_count = generate(
        args.n, args.cap, args.cup, args.strong)
    cnf_lines = [f"p cnf {len(all_triples)} {len(clauses)}"]
    cnf_lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    cnf = "\n".join(cnf_lines) + "\n"
    write_atomic(args.output, cnf)
    repo = Path(__file__).resolve().parent.parent
    manifest = {
        "schema_version": 1,
        "generator": "scripts/generate_signotope_state_sat.py",
        "revision": git_revision(repo),
        "n": args.n,
        "cap": args.cap,
        "cup": args.cup,
        "strong": args.strong,
        "variables": len(all_triples),
        "clauses": len(clauses),
        "clause_counts": counts,
        "strong_pattern_count": pattern_count,
        "triple_order": "lexicographic combinations(range(n), 3); DIMACS variables are one-based",
        "cnf": str(args.output),
        "cnf_sha256": hashlib.sha256(cnf.encode()).hexdigest(),
    }
    write_atomic(
        args.output.with_suffix(args.output.suffix + ".json"),
        json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
