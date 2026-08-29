#!/usr/bin/env python3
"""Independently audit the Fin13 predecessor-half CNF semantics."""

from __future__ import annotations

import argparse
import collections
import hashlib
import itertools
import json
from pathlib import Path


def parse_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = -1
    declared_clauses = -1
    clauses: list[tuple[int, ...]] = []
    for line in path.read_text().splitlines():
        if not line or line.startswith("c"):
            continue
        if line.startswith("p cnf "):
            _, _, raw_variables, raw_clauses = line.split()
            variables = int(raw_variables)
            declared_clauses = int(raw_clauses)
            continue
        values = tuple(map(int, line.split()))
        if not values or values[-1] != 0:
            raise ValueError("unterminated clause")
        clauses.append(values[:-1])
    if variables < 0 or len(clauses) != declared_clauses:
        raise ValueError("DIMACS header mismatch")
    return variables, clauses


def forbidden(keys: list[int], bits: tuple[bool, ...]) -> tuple[int, ...]:
    return tuple(-key if bit else key for key, bit in zip(keys, bits))


def is_strong_assignment(
    triples: list[tuple[int, int, int]], bits: tuple[bool, ...]
) -> bool:
    color = dict(zip(triples, bits))
    vertices = sorted({vertex for triple in triples for vertex in triple})
    for i, j, k, l in itertools.combinations(vertices, 4):
        if color[i, j, k] != color[i, j, l]:
            return False
        if color[i, k, l] != color[j, k, l]:
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()

    variables, clauses = parse_dimacs(args.cnf)
    manifest = json.loads(args.manifest.read_text())
    digest = hashlib.sha256(args.cnf.read_bytes()).hexdigest()
    if digest != manifest["cnf_sha256"]:
        raise ValueError("CNF hash mismatch")
    if variables != 10582 or len(clauses) != 137852:
        raise ValueError("frozen dimensions changed")

    triples = list(itertools.combinations(range(13), 3))
    triple_variable = {triple: i + 1 for i, triple in enumerate(triples)}
    by_length: dict[int, list[tuple[int, ...]]] = collections.defaultdict(list)
    for clause in clauses:
        if len(set(map(abs, clause))) != len(clause):
            raise ValueError("duplicate variable within clause")
        by_length[len(clause)].append(clause)
    if set(by_length) != {2, 4, 20, 168}:
        raise ValueError("unexpected clause length")

    expected_one_change = set()
    for a, b, c, d in itertools.combinations(range(13), 4):
        keys = [
            triple_variable[a, b, c],
            triple_variable[a, b, d],
            triple_variable[a, c, d],
            triple_variable[b, c, d],
        ]
        for bits in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(bits, bits[1:])) > 1:
                expected_one_change.add(forbidden(keys, bits))
    if set(by_length[4]) != expected_one_change or len(by_length[4]) != 5720:
        raise ValueError("one-change clause family mismatch")

    expected_no_six = set()
    for subset in itertools.combinations(range(13), 6):
        local_triples = list(itertools.combinations(subset, 3))
        keys = [triple_variable[triple] for triple in local_triples]
        for middle_bits in itertools.product((False, True), repeat=4):
            bits = tuple(middle_bits[subset.index(triple[1]) - 1] for triple in local_triples)
            if not is_strong_assignment(local_triples, bits):
                raise AssertionError("middle-determined assignment is not strong")
            expected_no_six.add(forbidden(keys, bits))
    if set(by_length[20]) != expected_no_six or len(by_length[20]) != 27456:
        raise ValueError("strong-six exclusion family mismatch")

    selector_requirements: dict[int, dict[int, bool]] = collections.defaultdict(dict)
    for clause in by_length[2]:
        if clause[0] >= 0 or abs(clause[0]) <= 286 or abs(clause[1]) > 286:
            raise ValueError("malformed selector implication")
        selector = abs(clause[0])
        triple_index = abs(clause[1])
        bit = clause[1] > 0
        if triple_index in selector_requirements[selector]:
            raise ValueError("duplicate selector requirement")
        selector_requirements[selector][triple_index] = bit
    if set(selector_requirements) != set(range(287, 10583)):
        raise ValueError("selector variable interval mismatch")

    selectors_by_five: dict[tuple[int, ...], list[int]] = collections.defaultdict(list)
    selector_pattern: dict[int, tuple[bool, ...]] = {}
    for selector, requirements in selector_requirements.items():
        if len(requirements) != 10:
            raise ValueError("selector does not bind ten triples")
        local_triples = [triples[index - 1] for index in requirements]
        vertices = tuple(sorted({vertex for triple in local_triples for vertex in triple}))
        if len(vertices) != 5 or set(local_triples) != set(itertools.combinations(vertices, 3)):
            raise ValueError("selector does not bind one complete five-set")
        ordered_triples = list(itertools.combinations(vertices, 3))
        bits = tuple(requirements[triple_variable[triple]] for triple in ordered_triples)
        if not is_strong_assignment(ordered_triples, bits):
            raise ValueError("selector binds a non-strong pattern")
        selectors_by_five[vertices].append(selector)
        selector_pattern[selector] = bits
    if len(selectors_by_five) != 1287:
        raise ValueError("five-set selector family incomplete")
    for five, selectors in selectors_by_five.items():
        if len(selectors) != 8 or len({selector_pattern[s] for s in selectors}) != 8:
            raise ValueError(f"strong patterns incomplete for {five}")

    seen_sevens = set()
    for clause in by_length[168]:
        if any(literal <= 286 for literal in clause):
            raise ValueError("seven-set clause contains a nonselector")
        five_sets = [five for five, selectors in selectors_by_five.items() if set(selectors) & set(clause)]
        vertices = tuple(sorted({vertex for five in five_sets for vertex in five}))
        if len(vertices) != 7:
            raise ValueError("coverage clause does not identify one seven-set")
        expected = {
            selector
            for five in itertools.combinations(vertices, 5)
            for selector in selectors_by_five[five]
        }
        if set(clause) != expected or len(clause) != len(expected):
            raise ValueError("seven-set coverage clause mismatch")
        seen_sevens.add(vertices)
    if seen_sevens != set(itertools.combinations(range(13), 7)):
        raise ValueError("seven-set family incomplete")

    receipt = {
        "schema_version": 1,
        "terminal": "FIN13-CNF-SEMANTICS-CHECKED",
        "cnf_sha256": digest,
        "variables": variables,
        "clauses": len(clauses),
        "one_change_clauses": len(by_length[4]),
        "no_strong_six_clauses": len(by_length[20]),
        "selector_implications": len(by_length[2]),
        "seven_coverage_clauses": len(by_length[168]),
        "five_sets": len(selectors_by_five),
        "seven_sets": len(seen_sevens),
    }
    args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
