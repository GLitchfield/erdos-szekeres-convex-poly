#!/usr/bin/env python3
"""Generate the anchored corrected Fin15 predecessor-half instance.

The clause stream reproduces the Ticket 0098 corrected semantic formula
(4,823 variables, 62,218 clauses: triple colors 1..455, strong-quad atoms
456..1820, strong-five atoms 1821..4823; categories in the order
``one_change``, ``strong_quad_definition``, ``strong_five_definition``,
``no_strong_six``, ``every_eight_has_strong_five``) and appends the 91
``anchor`` unit clauses forcing every triple through vertex ``0`` to a right
turn.  ``AnchoredPresentation.lean`` proves that this is a legitimate
normalization of every sweep-realizable coloring, and
``AnchoredFin15Consumer.lean`` turns a refutation of this instance into the
fifteen/sixteen middle producer of the fixed-six predecessor-half theorem.

The negated candidate encoded here: a one-change coloring on fifteen
vertices with no strong six-set in which every eight-set contains a strong
five-set.  Unsatisfiability therefore says every anchored strong-six-free
one-change coloring on fifteen vertices has a strong-five-free eight-set.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

N = 15
TRIPLES = tuple(itertools.combinations(range(N), 3))
QUADS = tuple(itertools.combinations(range(N), 4))
FIVES = tuple(itertools.combinations(range(N), 5))
TVAR = {triple: i + 1 for i, triple in enumerate(TRIPLES)}
QVAR = {quad: len(TVAR) + i + 1 for i, quad in enumerate(QUADS)}
FVAR = {five: len(TVAR) + len(QVAR) + i + 1 for i, five in enumerate(FIVES)}
TRIPLE_BY_VAR = {v: k for k, v in TVAR.items()}
QUAD_BY_VAR = {v: k for k, v in QVAR.items()}
FIVE_BY_VAR = {v: k for k, v in FVAR.items()}
UNANCHORED_SHA256 = "6a1ad5ff799cecbe5214e14e84cd851cc87fd97d6097f3a809a784285e835e63"
ANCHORED_SHA256 = "cb5c9fae96b9dfdebcf838ec509ab53a8c4ac82d385a01470980319dd5451073"


def quad_triples(quad):
    a, b, c, d = quad
    return ((a, b, c), (a, b, d), (a, c, d), (b, c, d))


def blocker(variables, bits):
    return tuple(-variable if bit else variable for variable, bit in zip(variables, bits))


def one_change_allowed(bits) -> bool:
    return sum(a != b for a, b in zip(bits, bits[1:])) <= 1


def corrected_strong_quad(bits) -> bool:
    return bits[0] == bits[1] and bits[2] == bits[3]


def annotated_formula():
    entries = []

    def add(category, clause, origin):
        entries.append({
            "id": len(entries) + 1,
            "category": category,
            "literals": tuple(clause),
            "origin": origin,
        })

    for quad in QUADS:
        variables = [TVAR[t] for t in quad_triples(quad)]
        for bits in itertools.product((False, True), repeat=4):
            if not one_change_allowed(bits):
                add("one_change", blocker(variables, bits), {"quad": quad, "bits": bits})
    for quad in QUADS:
        variables = [TVAR[t] for t in quad_triples(quad)]
        for extension in itertools.product((False, True), repeat=5):
            bits = extension[:4]
            strong_bit = extension[4]
            if strong_bit != corrected_strong_quad(bits):
                add("strong_quad_definition",
                    blocker(variables + [QVAR[quad]], extension),
                    {"quad": quad, "bits": bits, "strong": strong_bit})
    for five in FIVES:
        qvars = [QVAR[quad] for quad in itertools.combinations(five, 4)]
        for qvar in qvars:
            add("strong_five_definition", (-FVAR[five], qvar), {"five": five})
        add("strong_five_definition", (FVAR[five], *(-q for q in qvars)), {"five": five})
    for six in itertools.combinations(range(N), 6):
        add("no_strong_six",
            tuple(-FVAR[five] for five in itertools.combinations(six, 5)),
            {"six": six})
    for eight in itertools.combinations(range(N), 8):
        add("every_eight_has_strong_five",
            tuple(FVAR[five] for five in itertools.combinations(eight, 5)),
            {"eight": eight})
    unanchored = len(entries)
    for i, j in itertools.combinations(range(1, N), 2):
        add("anchor", (-TVAR[(0, i, j)],), {"triple": (0, i, j)})
    return entries, unanchored


def dimacs(entries, count) -> str:
    lines = [f"p cnf {len(TVAR) + len(QVAR) + len(FVAR)} {count}"]
    lines.extend(" ".join(map(str, e["literals"])) + " 0" for e in entries[:count])
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    entries, unanchored = annotated_formula()
    plain = dimacs(entries, unanchored)
    plain_digest = hashlib.sha256(plain.encode()).hexdigest()
    if plain_digest != UNANCHORED_SHA256:
        raise SystemExit(f"unanchored CNF digest mismatch: {plain_digest}")
    text = dimacs(entries, len(entries))
    digest = hashlib.sha256(text.encode()).hexdigest()
    if digest != ANCHORED_SHA256:
        raise SystemExit(f"anchored CNF digest mismatch: {digest}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text)
    counts = {}
    for e in entries:
        counts[e["category"]] = counts.get(e["category"], 0) + 1
    manifest = {
        "schema_version": 1,
        "generator": "scripts/generate_fin15_anchored_sat.py",
        "n": N,
        "variables": len(TVAR) + len(QVAR) + len(FVAR),
        "clauses": len(entries),
        "clause_counts": counts,
        "unanchored_cnf_sha256": plain_digest,
        "cnf_sha256": digest,
    }
    args.output.with_suffix(".cnf.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, sort_keys=True))


if __name__ == "__main__":
    main()
