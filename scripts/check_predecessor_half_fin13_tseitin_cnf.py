#!/usr/bin/env python3
"""Independently reconstruct and audit the compact Fin13 CNF."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def parse(path: Path):
    header = None
    clauses = []
    for line in path.read_text().splitlines():
        if line.startswith("p cnf "):
            _, _, variables, count = line.split()
            header = (int(variables), int(count))
        elif line and not line.startswith("c"):
            values = tuple(map(int, line.split()))
            if values[-1] != 0:
                raise ValueError("unterminated clause")
            clauses.append(values[:-1])
    if header is None or header[1] != len(clauses):
        raise ValueError("header mismatch")
    return header[0], clauses


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()

    variables, clauses = parse(args.cnf)
    triples = tuple(itertools.combinations(range(13), 3))
    quads = tuple(itertools.combinations(range(13), 4))
    fives = tuple(itertools.combinations(range(13), 5))
    tvar = {triple: i + 1 for i, triple in enumerate(triples)}
    qvar = {quad: len(tvar) + i + 1 for i, quad in enumerate(quads)}
    fvar = {five: len(tvar) + len(qvar) + i + 1 for i, five in enumerate(fives)}
    expected = []

    for a, b, c, d in quads:
        keys = [tvar[a, b, c], tvar[a, b, d], tvar[a, c, d], tvar[b, c, d]]
        for bits in itertools.product((False, True), repeat=4):
            block = tuple(-key if bit else key for key, bit in zip(keys, bits))
            if sum(x != y for x, y in zip(bits, bits[1:])) > 1:
                expected.append(block)
        for bits in itertools.product((False, True), repeat=4):
            block = tuple(-key if bit else key for key, bit in zip(keys, bits))
            strong = bits[0] == bits[1] and bits[2] == bits[3]
            expected.append(block + ((qvar[a, b, c, d] if strong else -qvar[a, b, c, d]),))

    for five in fives:
        qvars = [qvar[quad] for quad in itertools.combinations(five, 4)]
        expected.extend((-fvar[five], q) for q in qvars)
        expected.append((fvar[five], *(-q for q in qvars)))
    for six in itertools.combinations(range(13), 6):
        expected.append(tuple(-qvar[quad] for quad in itertools.combinations(six, 4)))
    for seven in itertools.combinations(range(13), 7):
        expected.append(tuple(fvar[five] for five in itertools.combinations(seven, 5)))

    if variables != 2288 or clauses != expected:
        raise ValueError("compact semantic reconstruction mismatch")
    manifest = json.loads(args.manifest.read_text())
    digest = hashlib.sha256(args.cnf.read_bytes()).hexdigest()
    if digest != manifest["cnf_sha256"]:
        raise ValueError("manifest hash mismatch")
    receipt = {
        "schema_version": 1,
        "terminal": "FIN13-TSEITIN-CNF-SEMANTICS-CHECKED",
        "cnf_sha256": digest,
        "variables": variables,
        "clauses": len(clauses),
        "reconstruction": "byte-order-equivalent independent implementation",
    }
    args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
