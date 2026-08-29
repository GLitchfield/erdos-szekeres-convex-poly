#!/usr/bin/env python3
"""Generate the compact Fin13 predecessor-half CNF with semantic atoms."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


N = 13
TRIPLES = tuple(itertools.combinations(range(N), 3))
QUADS = tuple(itertools.combinations(range(N), 4))
FIVES = tuple(itertools.combinations(range(N), 5))
TVAR = {triple: i + 1 for i, triple in enumerate(TRIPLES)}
QVAR = {quad: len(TVAR) + i + 1 for i, quad in enumerate(QUADS)}
FVAR = {five: len(TVAR) + len(QVAR) + i + 1 for i, five in enumerate(FIVES)}


def quad_triples(quad: tuple[int, int, int, int]):
    a, b, c, d = quad
    return ((a, b, c), (a, b, d), (a, c, d), (b, c, d))


def blocker(variables: list[int], bits: tuple[bool, ...]) -> tuple[int, ...]:
    return tuple(-variable if bit else variable for variable, bit in zip(variables, bits))


def annotated_formula():
    entries = []

    def add(category: str, clause, origin) -> None:
        entries.append({
            "id": len(entries) + 1,
            "category": category,
            "literals": tuple(clause),
            "origin": origin,
        })

    for quad in QUADS:
        variables = [TVAR[triple] for triple in quad_triples(quad)]
        for bits in itertools.product((False, True), repeat=4):
            if sum(a != b for a, b in zip(bits, bits[1:])) > 1:
                add("one_change", blocker(variables, bits), {"quad": quad, "bits": bits})
        for bits in itertools.product((False, True), repeat=4):
            strong = bits[0] == bits[1] and bits[2] == bits[3]
            add(
                "strong_quad_definition",
                blocker(variables, bits) + ((QVAR[quad] if strong else -QVAR[quad]),),
                {"quad": quad, "bits": bits, "strong": strong},
            )

    for five in FIVES:
        qvars = [QVAR[quad] for quad in itertools.combinations(five, 4)]
        for qvar in qvars:
            add("strong_five_definition", (-FVAR[five], qvar), {"five": five})
        add("strong_five_definition", (FVAR[five], *(-qvar for qvar in qvars)), {"five": five})

    for six in itertools.combinations(range(N), 6):
        add(
            "no_strong_six",
            tuple(-QVAR[quad] for quad in itertools.combinations(six, 4)),
            {"six": six},
        )

    for seven in itertools.combinations(range(N), 7):
        add(
            "every_seven_has_strong_five",
            tuple(FVAR[five] for five in itertools.combinations(seven, 5)),
            {"seven": seven},
        )
    return tuple(entries)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()

    entries = annotated_formula()
    variable_count = len(TVAR) + len(QVAR) + len(FVAR)
    lines = [f"p cnf {variable_count} {len(entries)}"]
    lines.extend(" ".join(map(str, entry["literals"])) + " 0" for entry in entries)
    data = ("\n".join(lines) + "\n").encode()
    args.cnf.parent.mkdir(parents=True, exist_ok=True)
    args.cnf.write_bytes(data)

    category_counts = {
        category: sum(entry["category"] == category for entry in entries)
        for category in (
            "one_change",
            "strong_quad_definition",
            "strong_five_definition",
            "no_strong_six",
            "every_seven_has_strong_five",
        )
    }
    manifest = {
        "schema_version": 1,
        "encoding": "fin13-predecessor-half-semantic-tseitin-v1",
        "model_tier": "abstract-one-change",
        "n": N,
        "variables": variable_count,
        "clauses": len(entries),
        "variable_counts": {
            "triple": len(TVAR),
            "strong_quad": len(QVAR),
            "strong_five": len(FVAR),
        },
        "clause_counts": category_counts,
        "cnf_sha256": hashlib.sha256(data).hexdigest(),
        "semantics": (
            "one-change coloring; strong-quad and strong-five atoms defined "
            "exactly; no strong six-set; every seven-set has a strong five-set"
        ),
    }
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
