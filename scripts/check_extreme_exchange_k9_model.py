#!/usr/bin/env python3
"""Independent semantic replay for the k=9 extreme-exchange SAT models."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from check_diagonal_k9_semantics import AuditFailure, parse_cnf, replay_lrat


N = 17
TRIPLES = tuple(itertools.combinations(range(N), 3))
TRIPLE_INDEX = {triple: index for index, triple in enumerate(TRIPLES)}


def data(tag: str):
    if tag == "8-9":
        return tuple(range(8)), tuple(range(8, 17)), tuple(range(8, 16))
    if tag == "9-8":
        return tuple(range(9, 17)), tuple(range(9)), tuple(range(1, 9))
    raise ValueError(tag)


def expected_cnf(tag: str):
    small, big, core = data(tag)
    variables = {triple: index + 1 for index, triple in enumerate(TRIPLES)}
    clauses = []
    for vertices in itertools.combinations(range(N), 4):
        a, b, c, d = vertices
        local = ((a, b, c), (a, b, d), (a, c, d), (b, c, d))
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                clauses.append(tuple(-variables[key] if value else variables[key]
                                     for key, value in zip(local, values)))
    equality_var = {}
    next_variable = len(TRIPLES) + 1
    for vertices in itertools.combinations(range(N), 4):
        a, b, c, d = vertices
        for side, (left, right) in enumerate(
                (((a, b, c), (a, b, d)), ((a, c, d), (b, c, d)))):
            equality_var[vertices, side] = next_variable
            x, y, e = variables[left], variables[right], next_variable
            clauses.extend(((-e, -x, y), (-e, x, -y), (e, x, y), (e, -x, -y)))
            next_variable += 1
    for vertices in itertools.combinations(range(N), 4):
        clauses.append(tuple(variables[triple]
                             for triple in itertools.combinations(vertices, 3)))
    for vertices in itertools.combinations(range(N), 10):
        clause = []
        for quad in itertools.combinations(vertices, 4):
            clause.extend((-equality_var[quad, 0], -equality_var[quad, 1]))
        clauses.append(tuple(clause))
    for block in (small, big):
        clauses.extend((variables[triple],)
                       for triple in itertools.combinations(block, 3))
    for p in small:
        vertices = tuple(sorted((*core, p)))
        clauses.append(tuple(-variables[triple]
                             for triple in itertools.combinations(vertices, 3)))
    text = f"p cnf {next_variable - 1} {len(clauses)}\n" + "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in clauses)
    return text.encode()


def replay(tag: str, bits: tuple[bool, ...]):
    small, big, core = data(tag)

    def turn(i, j, k):
        return bits[TRIPLE_INDEX[i, j, k]]

    one_change = True
    for a, b, c, d in itertools.combinations(range(N), 4):
        word = (turn(a, b, c), turn(a, b, d), turn(a, c, d), turn(b, c, d))
        if sum(x != y for x, y in zip(word, word[1:])) > 1:
            one_change = False
            break

    no_cap_four = all(
        any(turn(*triple) for triple in itertools.combinations(vertices, 3))
        for vertices in itertools.combinations(range(N), 4))

    no_strong_ten = True
    for vertices in itertools.combinations(range(N), 10):
        strong = True
        for a, b, c, d in itertools.combinations(vertices, 4):
            if turn(a, b, c) != turn(a, b, d) or turn(a, c, d) != turn(b, c, d):
                strong = False
                break
        if strong:
            no_strong_ten = False
            break

    cup_blocks = all(
        all(turn(*triple) for triple in itertools.combinations(block, 3))
        for block in (small, big))
    exchange_cups_absent = all(
        not all(turn(*triple) for triple in itertools.combinations(
            tuple(sorted((*core, p))), 3))
        for p in small)
    return {"one_change": one_change, "no_cap_four": no_cap_four,
            "no_strong_ten": no_strong_ten, "cup_blocks": cup_blocks,
            "exchange_cups_absent": exchange_cups_absent}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path,
                        default=Path("runs/agents/20260811-wave3/extreme-exchange"))
    args = parser.parse_args()
    output = {"schema_version": 1, "checks": {}}
    for tag in ("8-9", "9-8"):
        result = json.loads((args.input / f"result-{tag}.json").read_text())
        expected = expected_cnf(tag)
        expected_hash = hashlib.sha256(expected).hexdigest()
        cnf_path = Path(result["cnf"])
        semantic_checks = {
            "cnf_reconstructed": expected_hash == result["cnf_sha256"] ==
                hashlib.sha256(cnf_path.read_bytes()).hexdigest(),
            "corrupted_clause_map_rejected": hashlib.sha256(
                expected.replace(b" 0\n", b" 1 0\n", 1)).hexdigest() != expected_hash,
        }
        if result["status"] == "UNSAT":
            lrat_path = Path(result["lrat"])
            replay = replay_lrat(cnf_path, lrat_path)
            corrupted_rejected = False
            try:
                replay_lrat(cnf_path, lrat_path, corrupt_empty_hint=True)
            except AuditFailure:
                corrupted_rejected = True
            base = cnf_path.with_suffix("")
            core_cnf = Path(str(base) + "-core.cnf")
            core_lrat = Path(str(base) + "-core.lrat")
            core_map = json.loads(Path(str(base) + "-core-map.json").read_text())
            dense_cnf = Path(str(base) + "-dense.cnf")
            dense_lrat = Path(str(base) + "-dense.lrat")
            dense_map = json.loads(Path(str(base) + "-dense-map.json").read_text())
            _, full_clauses = parse_cnf(cnf_path)
            _, core_clauses = parse_cnf(core_cnf)
            selected = tuple(full_clauses[index - 1]
                             for index in core_map["old_original_clause_ids"])
            old_variables = dense_map["old_variable_ids"]
            variable_map = {old: new for new, old in enumerate(old_variables, 1)}
            expected_dense = tuple(
                tuple((1 if literal > 0 else -1) * variable_map[abs(literal)]
                      for literal in clause)
                for clause in core_clauses)
            _, dense_clauses = parse_cnf(dense_cnf)
            dense_replay = replay_lrat(dense_cnf, dense_lrat)
            dense_corrupted_rejected = False
            try:
                replay_lrat(dense_cnf, dense_lrat, corrupt_empty_hint=True)
            except AuditFailure:
                dense_corrupted_rejected = True
            checks = {**semantic_checks, "status": "UNSAT",
                      "lrat_replay": replay,
                      "lrat_hash_matches": hashlib.sha256(lrat_path.read_bytes()).hexdigest()
                        == result["lrat_sha256"],
                      "corrupted_final_hint_rejected": corrupted_rejected,
                      "core_original_clause_map_matches": selected == tuple(core_clauses),
                      "core_source_hashes_match":
                        core_map["source_cnf_sha256"] == result["cnf_sha256"] and
                        core_map["source_lrat_sha256"] == result["lrat_sha256"],
                      "dense_variable_map_matches": expected_dense == tuple(dense_clauses),
                      "dense_source_hashes_match":
                        dense_map["source_cnf_sha256"] == core_map["core_cnf_sha256"] and
                        dense_map["source_lrat_sha256"] == core_map["core_lrat_sha256"],
                      "dense_lrat_replay": dense_replay,
                      "dense_corrupted_final_hint_rejected": dense_corrupted_rejected}
            checks["all_pass"] = all(value for key, value in checks.items()
                                     if key not in {"status", "lrat_replay",
                                                    "dense_lrat_replay"})
            output["checks"][tag] = checks
            continue
        if result["status"] != "SAT":
            output["checks"][tag] = {**semantic_checks, "status": result["status"],
                                      "all_pass": False}
            continue
        encoded = result["triple_bits_lexicographic"]
        if len(encoded) != len(TRIPLES) or set(encoded) - {"0", "1"}:
            raise ValueError("invalid triple bit vector")
        bits = tuple(char == "1" for char in encoded)
        checks = {**semantic_checks, **replay(tag, bits)}
        small, _, _ = data(tag)
        corrupt = list(bits)
        corrupt[TRIPLE_INDEX[tuple(small[:3])]] = False
        checks["corrupted_forced_cup_rejected"] = not all(replay(tag, tuple(corrupt)).values())
        checks["all_pass"] = all(checks.values())
        output["checks"][tag] = checks
    output["all_results_verified"] = all(
        value.get("all_pass", False) for value in output["checks"].values())
    (args.input / "checker.json").write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(json.dumps(output, sort_keys=True))
    if not output["all_results_verified"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
