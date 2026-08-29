#!/usr/bin/env python3
"""Generate the hostile Fin13 predecessor-half CNF.

The primary variables color increasing triples.  The formula asks for an
abstract one-change coloring with no strong six-set in which every seven-set
contains a strong five-set.  A satisfying assignment is therefore a
counterexample to the proposed abstract Fin13 support theorem.  Unsatisfiability
is computational evidence for that theorem, not by itself a Lean proof.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


Triple = tuple[int, int, int]


def forbid_assignment(
    variables: dict[Triple, int], keys: list[Triple], bits: tuple[bool, ...]
) -> list[int]:
    return [-variables[key] if bit else variables[key] for key, bit in zip(keys, bits)]


def strong_patterns(size: int) -> tuple[list[Triple], list[tuple[bool, ...]]]:
    """Return all local triple assignments satisfying the strong law."""
    triples = list(itertools.combinations(range(size), 3))
    parent = list(range(len(triples)))
    index = {triple: i for i, triple in enumerate(triples)}

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
        union(index[i, j, k], index[i, j, l])
        union(index[i, k, l], index[j, k, l])

    roots = sorted({find(i) for i in range(len(triples))})
    component = {root: i for i, root in enumerate(roots)}
    patterns = []
    for values in itertools.product((False, True), repeat=len(roots)):
        patterns.append(tuple(values[component[find(i)]] for i in range(len(triples))))
    return triples, patterns


def generate(n: int) -> tuple[int, list[list[int]], dict[str, int]]:
    if n != 13:
        raise ValueError("the frozen hostile gate has n = 13")

    all_triples = list(itertools.combinations(range(n), 3))
    variables = {triple: i + 1 for i, triple in enumerate(all_triples)}
    clauses: list[list[int]] = []
    counts: dict[str, int] = {}

    before = len(clauses)
    for a, b, c, d in itertools.combinations(range(n), 4):
        keys = [(a, b, c), (a, b, d), (a, c, d), (b, c, d)]
        for bits in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(bits, bits[1:])) > 1:
                clauses.append(forbid_assignment(variables, keys, bits))
    counts["one_change"] = len(clauses) - before

    local_six, six_patterns = strong_patterns(6)
    before = len(clauses)
    for subset in itertools.combinations(range(n), 6):
        keys = [tuple(subset[i] for i in triple) for triple in local_six]
        for bits in six_patterns:
            clauses.append(forbid_assignment(variables, keys, bits))
    counts["no_strong_six"] = len(clauses) - before

    local_five, five_patterns = strong_patterns(5)
    selectors: dict[tuple[tuple[int, ...], int], int] = {}
    next_variable = len(variables) + 1
    for subset in itertools.combinations(range(n), 5):
        for pattern_index in range(len(five_patterns)):
            selectors[subset, pattern_index] = next_variable
            next_variable += 1

    before = len(clauses)
    for (subset, pattern_index), selector in selectors.items():
        keys = [tuple(subset[i] for i in triple) for triple in local_five]
        for key, bit in zip(keys, five_patterns[pattern_index]):
            clauses.append([-selector, variables[key] if bit else -variables[key]])
    counts["strong_five_selector_implications"] = len(clauses) - before

    before = len(clauses)
    for seven in itertools.combinations(range(n), 7):
        clause = []
        for five in itertools.combinations(seven, 5):
            for pattern_index in range(len(five_patterns)):
                clause.append(selectors[five, pattern_index])
        clauses.append(clause)
    counts["every_seven_has_strong_five"] = len(clauses) - before

    counts["triple_variables"] = len(variables)
    counts["selector_variables"] = len(selectors)
    counts["strong_five_patterns"] = len(five_patterns)
    counts["strong_six_patterns"] = len(six_patterns)
    return next_variable - 1, clauses, counts


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=13)
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()

    variable_count, clauses, counts = generate(args.n)
    lines = [f"p cnf {variable_count} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    cnf_bytes = ("\n".join(lines) + "\n").encode()
    args.cnf.parent.mkdir(parents=True, exist_ok=True)
    args.cnf.write_bytes(cnf_bytes)

    manifest = {
        "schema_version": 1,
        "model_tier": "abstract-one-change",
        "n": args.n,
        "candidate": (
            "Every one-change strong-six-free coloring on Fin 13 has a "
            "seven-point strong-five-free support"
        ),
        "cnf_semantics": (
            "Negation of the candidate: one-change, no strong six-set, and "
            "every seven-set contains a strong five-set"
        ),
        "variables": variable_count,
        "clauses": len(clauses),
        "counts": counts,
        "cnf_sha256": hashlib.sha256(cnf_bytes).hexdigest(),
        "outcome_ceiling": (
            "SAT refutes only the abstract Fin13 candidate until the model is "
            "independently checked; UNSAT is checked computation only until a "
            "certificate and Lean semantic extraction compile"
        ),
    }
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
