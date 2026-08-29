#!/usr/bin/env python3
"""Independently replay a SAT model for the Fin13 predecessor-half gate."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def parse_assignment(path: Path) -> set[int]:
    positive: set[int] = set()
    saw_sat = False
    for line in path.read_text().splitlines():
        if line.startswith("s "):
            saw_sat = "SATISFIABLE" in line and "UNSATISFIABLE" not in line
        if line.startswith("v "):
            for value in map(int, line.split()[1:]):
                if value > 0:
                    positive.add(value)
    if not saw_sat:
        raise ValueError("solver output does not report SATISFIABLE")
    return positive


def strong(color: dict[tuple[int, int, int], bool], subset: tuple[int, ...]) -> bool:
    for i, j, k, l in itertools.combinations(subset, 4):
        if color[i, j, k] != color[i, j, l]:
            return False
        if color[i, k, l] != color[j, k, l]:
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver-output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    if manifest["n"] != 13:
        raise ValueError("unexpected n")
    cnf_sha256 = hashlib.sha256(args.cnf.read_bytes()).hexdigest()
    if cnf_sha256 != manifest["cnf_sha256"]:
        raise ValueError("CNF hash mismatch")

    positive = parse_assignment(args.solver_output)
    triples = list(itertools.combinations(range(13), 3))
    color = {triple: index + 1 in positive for index, triple in enumerate(triples)}

    bad_quads = []
    for quad in itertools.combinations(range(13), 4):
        a, b, c, d = quad
        bits = [color[a, b, c], color[a, b, d], color[a, c, d], color[b, c, d]]
        if sum(x != y for x, y in zip(bits, bits[1:])) > 1:
            bad_quads.append(quad)

    strong_sixes = [subset for subset in itertools.combinations(range(13), 6) if strong(color, subset)]
    seven_without_five = []
    for seven in itertools.combinations(range(13), 7):
        if not any(strong(color, five) for five in itertools.combinations(seven, 5)):
            seven_without_five.append(seven)

    if bad_quads or strong_sixes or seven_without_five:
        raise ValueError(
            f"semantic replay failed: quads={len(bad_quads)}, "
            f"sixes={len(strong_sixes)}, seven={len(seven_without_five)}"
        )

    triple_bits = "".join("1" if color[triple] else "0" for triple in triples)
    receipt = {
        "schema_version": 1,
        "terminal": "FIN13-ABSTRACT-COUNTERMODEL-CHECKED",
        "model_tier": "abstract-one-change",
        "n": 13,
        "cnf_sha256": cnf_sha256,
        "solver_output_sha256": hashlib.sha256(args.solver_output.read_bytes()).hexdigest(),
        "triple_bits_sha256": hashlib.sha256(triple_bits.encode()).hexdigest(),
        "one_change_quadruples_checked": 715,
        "strong_six_subsets_checked": 1716,
        "seven_subsets_checked": 1716,
        "strong_six_count": 0,
        "seven_without_strong_five_count": 0,
        "scope_ceiling": (
            "Refutes the abstract OneChangeOn Fin13 window claim; it does not "
            "refute the sweep-realizable predecessor-half theorem"
        ),
    }
    args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
