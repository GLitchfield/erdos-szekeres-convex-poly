#!/usr/bin/env python3
"""Generate the anchored rank-three signotope instance for ES(6) = 17.

Variables are the 680 increasing triples of ``Fin 17`` in lexicographic
order (one-based); true means a left turn.  Clauses, in this order:

* ``one_change``: for every quadruple, the eight turn sequences with more
  than one change are forbidden (19,040 clauses);
* ``no_strong_six``: for every six-subset, the sixteen strong colorings
  (each middle vertex independently on the lower or upper chain) are
  forbidden (198,016 clauses);
* ``anchor``: every triple through vertex ``0`` is a right turn (120 unit
  clauses).  ``AnchoredPresentation.lean`` proves that this is a legitimate
  normalization of every sweep-realizable coloring.

Without the anchor units the instance is byte-identical, for ``n = 9`` and
``k = 5``, to ``certificates/es5-signotope.cnf``.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

N = 17
K = 6
ANCHORED_SHA256 = "11fb188b998da55b7664e78aabf7ba2c202afe8e2df3a28a3e849798146c74c0"


def triples(vertices):
    return list(itertools.combinations(vertices, 3))


TRIPLES = triples(range(N))
VAR = {t: index + 1 for index, t in enumerate(TRIPLES)}
TRIPLE_BY_VAR = {index + 1: t for index, t in enumerate(TRIPLES)}


def one_change(values) -> bool:
    return sum(a != b for a, b in zip(values, values[1:])) <= 1


def strong_patterns(k: int):
    """All strong colorings of ``k`` ordered vertices: a triple is a left
    turn iff its middle vertex is on the lower chain."""
    local = triples(range(k))
    patterns = []
    for assignment in itertools.product((False, True), repeat=k - 2):
        lower = {index + 1 for index in range(k - 2) if assignment[index]}
        patterns.append(tuple(b in lower for a, b, c in local))
    return patterns


def generate():
    """Return the clause records: (category, owner, values, literals)."""
    records = []
    for quad in itertools.combinations(range(N), 4):
        i, j, m, l = quad
        keys = ((i, j, m), (i, j, l), (i, m, l), (j, m, l))
        for values in itertools.product((False, True), repeat=4):
            if one_change(values):
                continue
            literals = tuple(-VAR[key] if value else VAR[key]
                             for key, value in zip(keys, values))
            records.append(("one_change", quad, values, literals))
    patterns = strong_patterns(K)
    for six in itertools.combinations(range(N), K):
        keys = triples(six)
        for values in patterns:
            literals = tuple(-VAR[key] if value else VAR[key]
                             for key, value in zip(keys, values))
            records.append(("no_strong_six", six, values, literals))
    for i, j in itertools.combinations(range(1, N), 2):
        records.append(("anchor", (0, i, j), (False,), (-VAR[(0, i, j)],)))
    return records


def dimacs(records) -> str:
    lines = [f"p cnf {len(TRIPLES)} {len(records)}"]
    lines.extend(" ".join(map(str, literals)) + " 0"
                 for _, _, _, literals in records)
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = generate()
    text = dimacs(records)
    digest = hashlib.sha256(text.encode()).hexdigest()
    if digest != ANCHORED_SHA256:
        raise SystemExit(f"anchored CNF digest mismatch: {digest}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text)
    counts = {}
    for category, _, _, _ in records:
        counts[category] = counts.get(category, 0) + 1
    manifest = {
        "schema_version": 1,
        "generator": "scripts/generate_es6_anchored_sat.py",
        "n": N,
        "k": K,
        "variables": len(TRIPLES),
        "clauses": len(records),
        "clause_counts": counts,
        "cnf_sha256": digest,
        "triple_order": "lexicographic combinations(range(17), 3); one-based",
        "anchor": "unit clauses forcing every triple (0, i, j) to a right turn",
    }
    args.output.with_suffix(".cnf.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, sort_keys=True))


if __name__ == "__main__":
    main()
