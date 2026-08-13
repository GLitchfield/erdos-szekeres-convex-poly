#!/usr/bin/env python3
"""Trim and renumber the frozen quotient-free mixed-567 encoding-A proof.

The transformation keeps precisely the transitive LRAT dependency cone of the
final empty clause.  It never changes a clause or a RUP hint chain; it only
removes unused initial/addition clauses, removes deletion lines, and renumbers
the retained database densely.  The independently written frozen checker is
run separately on every generated artifact.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass
from pathlib import Path


EXPECTED = {
    "cnf": "af1664224aa6cf1690d61f3d907f42217750662be182f97365ef12781e64f84c",
    "lrat": "c80efbed4d0647171c5ce79c3689c5f1a30f996cffaef74a8d335f1d23689008",
    "origins": "506ba25d61d39891e8a65a71bf70a0af3f7f71be7f040723844f9cafd510d8d7",
    "vars": "0a9ff91d4ba4c8c5d89aaaec6606d121993e6964f0ea090fec50643bca32a396",
}

LABELS = ("p", "q", "u0", "u1", "v0", "v1", "c", "d", "e0", "e1", "e2", "e3")
LABEL_INDEX = {label: index for index, label in enumerate(LABELS)}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def split_zero(values: list[int], start: int) -> tuple[list[int], int]:
    result: list[int] = []
    index = start
    while index < len(values):
        value = values[index]
        index += 1
        if value == 0:
            return result, index
        result.append(value)
    raise ValueError("missing zero terminator")


def parse_cnf(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = expected = None
    clauses: list[tuple[int, ...]] = []
    pending: list[int] = []
    for raw_line in path.read_text(encoding="ascii").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            fields = line.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise ValueError("malformed DIMACS header")
            variables, expected = map(int, fields[2:])
            continue
        if variables is None:
            raise ValueError("DIMACS clause before header")
        for field in line.split():
            literal = int(field)
            if literal:
                if abs(literal) > variables:
                    raise ValueError("literal exceeds variable bound")
                pending.append(literal)
            else:
                clauses.append(tuple(pending))
                pending = []
    if pending or variables is None or expected != len(clauses):
        raise ValueError("DIMACS count or termination mismatch")
    return variables, clauses


@dataclass(frozen=True)
class Addition:
    old_id: int
    clause: tuple[int, ...]
    hints: tuple[int, ...]


def parse_lrat(path: Path, initial_count: int) -> list[Addition]:
    additions: list[Addition] = []
    last_id = initial_count
    for line_number, raw_line in enumerate(
            path.read_text(encoding="ascii").splitlines(), start=1):
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        fields = line.split()
        proof_id = int(fields[0])
        if len(fields) >= 2 and fields[1] == "d":
            if proof_id < last_id:
                raise ValueError(f"backward deletion id at line {line_number}")
            last_id = proof_id
            continue
        if proof_id <= last_id:
            raise ValueError(f"non-increasing addition id at line {line_number}")
        last_id = proof_id
        values = [int(field) for field in fields[1:]]
        clause, hint_start = split_zero(values, 0)
        hints, end = split_zero(values, hint_start)
        if end != len(values) or not hints or any(hint <= 0 for hint in hints):
            raise ValueError(f"malformed pure-RUP addition at line {line_number}")
        additions.append(Addition(proof_id, tuple(clause), tuple(hints)))
    if not additions or additions[-1].clause:
        raise ValueError("LRAT does not end in an empty-clause addition")
    return additions


def dependency_cone(initial_count: int, additions: list[Addition]) -> tuple[set[int], set[int]]:
    by_id = {addition.old_id: addition for addition in additions}
    if len(by_id) != len(additions):
        raise ValueError("duplicate addition id")
    needed_initial: set[int] = set()
    needed_additions: set[int] = set()
    stack = [additions[-1].old_id]
    while stack:
        clause_id = stack.pop()
        if clause_id <= initial_count:
            if clause_id <= 0:
                raise ValueError("nonpositive initial clause dependency")
            needed_initial.add(clause_id)
            continue
        if clause_id in needed_additions:
            continue
        addition = by_id.get(clause_id)
        if addition is None:
            raise ValueError(f"dependency references missing addition {clause_id}")
        needed_additions.add(clause_id)
        stack.extend(addition.hints)
    return needed_initial, needed_additions


def write_core(variables: int, clauses: list[tuple[int, ...]], additions: list[Addition],
               origins_path: Path, output_dir: Path) -> dict[str, object]:
    needed_initial, needed_additions = dependency_cone(len(clauses), additions)
    initial_ids = sorted(needed_initial)
    retained_additions = [a for a in additions if a.old_id in needed_additions]
    renumber = {old_id: new_id for new_id, old_id in enumerate(initial_ids, start=1)}
    next_id = len(initial_ids) + 1
    for addition in retained_additions:
        renumber[addition.old_id] = next_id
        next_id += 1
    for addition in retained_additions:
        if any(hint not in renumber or renumber[hint] >= renumber[addition.old_id]
               for hint in addition.hints):
            raise ValueError("retained proof has an unavailable or future hint")

    output_dir.mkdir(parents=True, exist_ok=True)
    cnf_path = output_dir / "a-core.cnf"
    lrat_path = output_dir / "a-core.lrat"
    origins_output = output_dir / "a-core-origins.json"
    cnf_lines = [f"p cnf {variables} {len(initial_ids)}"]
    cnf_lines.extend(" ".join(map(str, clauses[old_id - 1])) + " 0"
                     for old_id in initial_ids)
    cnf_path.write_text("\n".join(cnf_lines) + "\n", encoding="ascii")
    lrat_lines = []
    for addition in retained_additions:
        clause = " ".join(map(str, addition.clause))
        hints = " ".join(str(renumber[hint]) for hint in addition.hints)
        lrat_lines.append(f"{renumber[addition.old_id]} {clause} 0 {hints} 0")
    lrat_path.write_text("\n".join(lrat_lines) + "\n", encoding="ascii")

    origin_document = json.loads(origins_path.read_text(encoding="utf-8"))
    origins = origin_document["origins"]
    if len(origins) != len(clauses):
        raise ValueError("origin count differs from initial CNF")
    core_origins = []
    for new_id, old_id in enumerate(initial_ids, start=1):
        record = dict(origins[old_id - 1])
        if record.get("clause_id") != old_id:
            raise ValueError("origin ID differs from its index")
        record["original_clause_id"] = old_id
        record["clause_id"] = new_id
        core_origins.append(record)
    origins_output.write_text(json.dumps({
        "schema_version": 1,
        "encoding": "a-core",
        "num_variables": variables,
        "num_clauses": len(initial_ids),
        "origins": core_origins,
    }, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    summary = {
        "schema_version": 1,
        "status": "generated",
        "variables": variables,
        "original_initial_clauses": len(clauses),
        "core_initial_clauses": len(initial_ids),
        "original_additions": len(additions),
        "core_additions": len(retained_additions),
        "original_empty_clause_id": additions[-1].old_id,
        "core_empty_clause_id": renumber[additions[-1].old_id],
        "hashes": {
            "core_cnf": sha256(cnf_path),
            "core_lrat": sha256(lrat_path),
            "core_origins": sha256(origins_output),
        },
    }
    (output_dir / "a-core-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def finset(values: list[int] | tuple[int, ...]) -> str:
    return "{" + ", ".join(map(str, values)) + "}"


def atom_name(variable: int) -> str:
    return f"Mixed567AllOrderAtom{variable:03d}"


def atom_term(variable: int) -> str:
    return f"({atom_name(variable)} χ embed)"


def failure_expression(clause: tuple[int, ...]) -> str:
    pieces = [f"¬{atom_term(literal)}" if literal > 0 else atom_term(-literal)
              for literal in clause]
    return " ∧\n      ".join(pieces)


def balanced_or(expressions: list[str], indent: int = 2) -> str:
    if not expressions:
        raise ValueError("cannot balance an empty disjunction")
    if len(expressions) == 1:
        return expressions[0]
    middle = len(expressions) // 2
    left = balanced_or(expressions[:middle], indent + 2)
    right = balanced_or(expressions[middle:], indent + 2)
    return f"({left} ∨\n{' ' * indent}{right})"


def tree_ranges(size: int, depth: int) -> list[tuple[int, int]]:
    ranges = [(0, size)]
    for _ in range(depth):
        next_ranges = []
        for start, stop in ranges:
            middle = start + (stop - start) // 2
            next_ranges.extend(((start, middle), (middle, stop)))
        ranges = next_ranges
    return ranges


def semantic_data(vars_path: Path, core_dir: Path):
    if sha256(vars_path) != EXPECTED["vars"]:
        raise ValueError("frozen variable-map hash mismatch")
    document = json.loads(vars_path.read_text())
    by_variable: dict[int, dict[str, object]] = {}
    for record in document["pair_variables"]:
        by_variable[record["variable"]] = {
            "kind": "pair",
            "support": [LABEL_INDEX[record["left"]], LABEL_INDEX[record["right"]]],
        }
    for record in document["triple_variables"]:
        by_variable[record["variable"]] = {
            "kind": "triple",
            "support": [LABEL_INDEX[label] for label in record["support"]],
        }
    for record in document["strong_four_variables"]:
        by_variable[record["variable"]] = {
            "kind": "strong",
            "support": [LABEL_INDEX[label] for label in record["support"]],
        }
    if sorted(by_variable) != list(range(1, 782)):
        raise ValueError("variable map is not the exact 781-atom vocabulary")
    variables, clauses = parse_cnf(core_dir / "a-core.cnf")
    origins = json.loads((core_dir / "a-core-origins.json").read_text())["origins"]
    if variables != 781 or len(clauses) != len(origins):
        raise ValueError("core semantics dimensions mismatch")
    return by_variable, clauses, origins


def atoms_text(by_variable: dict[int, dict[str, object]]) -> str:
    lines = ["-- Generated by scripts/generate_mixed567_all_order_lean.py; do not edit.",
             "module", "", "public import ErdosSzekeres.Mixed567AllOrderEncoding", "",
             "@[expose] public section", "", "namespace ErdosSzekeres", "",
             "set_option maxHeartbeats 0", "set_option maxRecDepth 20000", ""]
    for variable in range(1, 782):
        record = by_variable[variable]
        support = record["support"]
        if record["kind"] == "pair":
            a, b = support
            body = f"embed {a} < embed {b}"
        elif record["kind"] == "triple":
            body = f"Mixed567ColorAtom χ embed {finset(support)} (by decide)"
        else:
            body = f"Mixed567StrongAtom χ embed {finset(support)}"
        lines += [f"def {atom_name(variable)} {{n : ℕ}} (χ : TripleColoring n)",
                  f"    (embed : Fin 12 ↪ Fin n) : Prop := {body}", ""]
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def intro_failure(clause: tuple[int, ...]) -> list[str]:
    hypotheses = [f"h{i}" for i in range(len(clause))]
    if len(clause) == 1:
        return [f"  intro {hypotheses[0]}"]
    return [f"  rintro ⟨{', '.join(hypotheses)}⟩"]


def unfold_hypotheses(clause: tuple[int, ...]) -> list[str]:
    names = [atom_name(abs(literal)) for literal in clause]
    lines = ["  unfold " + names[0]]
    for name in names[1:]:
        if len(lines[-1]) + len(name) + 1 < 96:
            lines[-1] += " " + name
        else:
            lines.append("    " + name)
    lines[-1] += " at *"
    return lines


def ordered_color_data(order: list[int]):
    a, b, c, d = order
    return [(a, b, c), (a, b, d), (a, c, d), (b, c, d)]


def semantic_clause_lemma(index: int, clause: tuple[int, ...], origin: dict[str, object],
                          by_variable: dict[int, dict[str, object]]) -> list[str]:
    kind = origin["kind"]
    name = f"mixed567AllOrder_clause{index + 1:05d}_valid"
    inputs = ["    (χ : TripleColoring n) (embed : Fin 12 ↪ Fin n)"]
    if kind == "one_change_forbidden_word":
        inputs.append("    (hone : OneChangeOn χ (Finset.univ.image embed))")
    elif kind == "canonical_witness_strong_four":
        inputs += ["    (hA0 : IsStrongPolygonSet χ (mixed567A0.image embed))",
                   "    (hA1 : IsStrongPolygonSet χ (mixed567A1.image embed))",
                   "    (hB0 : IsStrongPolygonSet χ (mixed567B0.image embed))",
                   "    (hB1 : IsStrongPolygonSet χ (mixed567B1.image embed))",
                   "    (hD0 : IsStrongPolygonSet χ (mixed567D0.image embed))",
                   "    (hD1 : IsStrongPolygonSet χ (mixed567D1.image embed))"]
    elif kind in {"no_cap_five", "no_cup_six", "no_strong_seven"}:
        inputs.append("    (hno : ¬ContainsTarget567 χ (Finset.univ.image embed))")
    lines = [f"theorem {name} {{n : ℕ}}", *inputs,
             f"    : ¬({failure_expression(clause)}) := by"]
    lines += intro_failure(clause)
    lines += unfold_hypotheses(clause)

    if kind.startswith("order_transitivity_"):
        labels = [LABEL_INDEX[label] for label in origin["labels"]]
        for number, (a, b) in enumerate(itertools.combinations(labels, 2)):
            lines.append(f"  have hne{number} : embed {a} ≠ embed {b} := "
                         f"embed.injective.ne (by decide)")
        lines.append("  omega")
        return lines + [""]

    if kind in {"strong_four_reification", "one_change_forbidden_word"}:
        order = [LABEL_INDEX[label] for label in origin["order"]]
        a, b, c, d = order
        pair_hypotheses = [i for i, literal in enumerate(clause)
                           if by_variable[abs(literal)]["kind"] == "pair"]
        for number, (x, y) in enumerate(zip(order, order[1:])):
            lines.append(f"  have hne{number} : embed {x} ≠ embed {y} := "
                         f"embed.injective.ne (by decide)")
        lines += [f"  have hab : embed {a} < embed {b} := by omega",
                  f"  have hbc : embed {b} < embed {c} := by omega",
                  f"  have hcd : embed {c} < embed {d} := by omega"]
        triples = ordered_color_data(order)
        for number, triple in enumerate(triples):
            variable = next(variable for variable, record in by_variable.items()
                            if record["kind"] == "triple" and
                            set(record["support"]) == set(triple))
            support = by_variable[variable]["support"]
            x, y, z = triple
            left_order = "hab" if (x, y) == (a, b) else (
                "hab.trans hbc" if (x, y) == (a, c) else "hbc")
            right_order = "hbc" if (y, z) == (b, c) else (
                "hbc.trans hcd" if (y, z) == (b, d) else "hcd")
            lines += [f"  have heq{number} := mixed567ColorAtom_eq_of_order χ embed",
                      f"    {finset(support)} (by decide) {x} {y} {z} (by decide)",
                      f"    ({left_order}) ({right_order})"]
        if kind == "one_change_forbidden_word":
            lines += [f"  have hallowed := hone (i := embed {a}) (j := embed {b})",
                      f"    (k := embed {c}) (l := embed {d}) hab hbc hcd",
                      "    (by simp) (by simp) (by simp) (by simp)"]
        else:
            strong_variable = next(abs(literal) for literal in clause
                                   if by_variable[abs(literal)]["kind"] == "strong")
            support = by_variable[strong_variable]["support"]
            lines += ["  have hstrong := mixed567StrongAtom_iff_of_order χ embed",
                      f"    {finset(support)} {a} {b} {c} {d} (by decide) hab hbc hcd"]
        for number, triple in enumerate(triples):
            x, y, z = triple
            left_order = "hab" if (x, y) == (a, b) else (
                "hab.trans hbc" if (x, y) == (a, c) else "hbc")
            right_order = "hbc" if (y, z) == (b, c) else (
                "hbc.trans hcd" if (y, z) == (b, d) else "hcd")
            lines.append(f"  cases hcolor{number} : χ ⟨embed {x}, embed {y}, embed {z}, "
                         f"{left_order}, {right_order}⟩ <;>")
        suffix = "TurnSequenceAllowed" if kind == "one_change_forbidden_word" else ""
        lines.append(f"    simp_all [{suffix}]" if suffix else "    simp_all")
        return lines + [""]

    if kind == "canonical_witness_strong_four":
        variable = abs(clause[0])
        support = by_variable[variable]["support"]
        witnesses = origin["witnesses"]
        witness = witnesses[0]
        lines += [f"  apply h0", f"  exact mixed567StrongAtom_mono h{witness}",
                  f"    (by decide : {finset(support)} ⊆ mixed567{witness})"]
        return lines + [""]

    support = [LABEL_INDEX[label] for label in origin["support"]]
    subset_size = 4 if kind == "no_strong_seven" else 3
    subsets = list(itertools.combinations(support, subset_size))
    typed_support = f"(show Finset (Fin 12) from {finset(support)})"
    enumerated_subsets = finset([finset(subset) for subset in subsets])
    lines += ["  have henum :",
              f"      {typed_support}.powersetCard {subset_size} =",
              f"        (show Finset (Finset (Fin 12)) from {enumerated_subsets}) := by decide"]
    if kind == "no_cap_five":
        lines += ["  apply hno", "  apply Or.inl", f"  refine ⟨{typed_support}.image embed, ?_, ?_, ?_⟩",
                  "  · exact Finset.image_mono embed (by simp)",
                  "  · simp [Finset.card_image_of_injective _ embed.injective]",
                  "  · apply isTurnPolygonSet_image_of_colorAtoms (cardinality := 5) χ embed",
                  f"      {typed_support} (by decide) Turn.right", "    intro triple htriple",
                  "    rw [henum] at htriple",
                  "    simp only [Finset.mem_insert, Finset.mem_singleton] at htriple",
                  "    rcases htriple with " + " | ".join("rfl" for _ in subsets)]
    elif kind == "no_cup_six":
        lines += ["  apply hno", "  apply Or.inr", "  apply Or.inl",
                  f"  refine ⟨{typed_support}.image embed, ?_, ?_, ?_⟩",
                  "  · exact Finset.image_mono embed (by simp)",
                  "  · simp [Finset.card_image_of_injective _ embed.injective]",
                  "  · apply isTurnPolygonSet_image_of_colorAtoms (cardinality := 6) χ embed",
                  f"      {typed_support} (by decide) Turn.left", "    intro triple htriple",
                  "    rw [henum] at htriple",
                  "    simp only [Finset.mem_insert, Finset.mem_singleton] at htriple",
                  "    rcases htriple with " + " | ".join("rfl" for _ in subsets)]
    else:
        lines += ["  apply hno", "  apply Or.inr", "  apply Or.inr",
                  f"  refine ⟨{typed_support}.image embed, ?_, ?_, ?_⟩",
                  "  · exact Finset.image_mono embed (by simp)",
                  "  · simp [Finset.card_image_of_injective _ embed.injective]",
                  f"  · apply isStrongPolygonSet_image_of_strongAtoms χ embed {typed_support}",
                  "    intro four hfour",
                  "    rw [henum] at hfour",
                  "    simp only [Finset.mem_insert, Finset.mem_singleton] at hfour",
                  "    rcases hfour with " + " | ".join("rfl" for _ in subsets)]
    literal_hypothesis = {abs(literal): f"h{i}" for i, literal in enumerate(clause)}
    for subset in subsets:
        variable = next(variable for variable, record in by_variable.items()
                        if record["kind"] == ("strong" if subset_size == 4 else "triple")
                        and set(record["support"]) == set(subset))
        lines.append(f"    · exact {literal_hypothesis[variable]}")
    return lines + [""]


def chunk_text(index: int, start: int, stop: int, clauses, origins, by_variable) -> str:
    lines = ["-- Generated by scripts/generate_mixed567_all_order_lean.py; do not edit.",
             "module", "", "public import ErdosSzekeres.Mixed567AllOrderAtoms", "",
             "@[expose] public section", "", "namespace ErdosSzekeres", "",
             "set_option maxHeartbeats 0", "set_option maxRecDepth 20000", "",
             f"/-! Exact semantic clauses {start} through {stop - 1} of encoding A. -/", ""]
    for dense_index in range(start, stop):
        lines += semantic_clause_lemma(dense_index, clauses[dense_index], origins[dense_index],
                                       by_variable)
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def clause_invocation(index: int, origin: dict[str, object]) -> str:
    lemma = f"mixed567AllOrder_clause{index + 1:05d}_valid χ embed"
    kind = origin["kind"]
    if kind == "one_change_forbidden_word":
        return lemma + " hone"
    if kind == "canonical_witness_strong_four":
        return lemma + " hA0 hA1 hB0 hB1 hD0 hD1"
    if kind in {"no_cap_five", "no_cup_six", "no_strong_seven"}:
        return lemma + " hno"
    return lemma


def eliminator_text(index: int, start: int, stop: int, chunk_size: int,
                    clauses, origins) -> str:
    first_chunk = start // chunk_size
    last_chunk = (stop - 1) // chunk_size
    name = f"Mixed567AllOrderBadSubtree{index:03d}"
    lines = ["-- Generated by scripts/generate_mixed567_all_order_lean.py; do not edit.",
             "module", ""]
    lines += [f"public import ErdosSzekeres.Mixed567AllOrderSemanticChunk{i:03d}"
              for i in range(first_chunk, last_chunk + 1)]
    lines += ["", "@[expose] public section", "", "namespace ErdosSzekeres", "",
              "set_option maxHeartbeats 0", "set_option maxRecDepth 20000", "",
              f"def {name} {{n : ℕ}} (χ : TripleColoring n)",
              "    (embed : Fin 12 ↪ Fin n) : Prop :="]
    failures = [failure_expression(clauses[i]) for i in range(start, stop)]
    lines.append("  " + balanced_or(failures).replace("\n", "\n  "))
    lines += ["", f"theorem {name}_impossible {{n : ℕ}}",
              "    (χ : TripleColoring n) (embed : Fin 12 ↪ Fin n)",
              "    (hone : OneChangeOn χ (Finset.univ.image embed))",
              "    (hA0 : IsStrongPolygonSet χ (mixed567A0.image embed))",
              "    (hA1 : IsStrongPolygonSet χ (mixed567A1.image embed))",
              "    (hB0 : IsStrongPolygonSet χ (mixed567B0.image embed))",
              "    (hB1 : IsStrongPolygonSet χ (mixed567B1.image embed))",
              "    (hD0 : IsStrongPolygonSet χ (mixed567D0.image embed))",
              "    (hD1 : IsStrongPolygonSet χ (mixed567D1.image embed))",
              "    (hno : ¬ContainsTarget567 χ (Finset.univ.image embed)) :",
              f"    ¬{name} χ embed := by", "  intro hbad", "  simp only [", f"    {name},"]
    for i in range(start, stop):
        lines.append(f"    {clause_invocation(i, origins[i])},")
    lines += ["    false_or, or_false", "  ] at hbad", "", "end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def final_text(clauses, ranges, by_variable) -> str:
    lines = ["-- Generated by scripts/generate_mixed567_all_order_lean.py; do not edit.",
             "module", "", "public import ErdosSzekeres.Mixed567AllOrderCheckpointSegment031"]
    lines += [f"public import ErdosSzekeres.Mixed567AllOrderSemanticElim{i:03d}"
              for i in range(len(ranges))]
    lines += ["", "@[expose] public section", "", "namespace ErdosSzekeres", "",
              "set_option maxHeartbeats 0", "set_option maxRecDepth 20000", "",
              "def Mixed567AllOrderBadTree {n : ℕ} (χ : TripleColoring n)",
              "    (embed : Fin 12 ↪ Fin n) : Prop :="]
    names = [f"Mixed567AllOrderBadSubtree{i:03d} χ embed" for i in range(len(ranges))]
    lines.append("  " + balanced_or(names).replace("\n", "\n  "))
    lines += ["", "/-- Exact quotient-free arbitrary-placement finite mixed state-567 theorem. -/",
              "theorem mixed567AllOrderFiniteTheorem : Mixed567FiniteTheorem := by",
              "  intro n χ embed hone hA0 hA1 hB0 hB1 hD0 hD1", "  by_contra hno",
              "  have hbad := Mixed567AllOrderCheckpoint.publicUnsat"]
    atoms = [atom_term(i) for i in range(1, 782)]
    for start in range(0, len(atoms), 4):
        lines.append("    " + " ".join(atoms[start:start + 4]))
    lines += ["  change Mixed567AllOrderBadTree χ embed at hbad",
              "  simpa only [Mixed567AllOrderBadTree,"]
    for i in range(len(ranges)):
        lines.append(f"    Mixed567AllOrderBadSubtree{i:03d}_impossible χ embed "
                     "hone hA0 hA1 hB0 hB1 hD0 hD1 hno,")
    lines += ["    false_or, or_false", "  ] using hbad", "",
              "/-- The exact mixed carrier-only omission normal form forces the 5/6/7 target. -/",
              "theorem mixedCarrierOnlyOmissionNormalForm_forces_target567",
              "    {n : ℕ} {χ : TripleColoring n}",
              "    {first second : Finset (Fin n)}",
              "    {witnesses : Finset (Finset (Fin n))}",
              "    (hsystem : IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)",
              "    (hfirstCard : first.card = 6) (hsecondCard : second.card = 6)",
              "    (hcarrierDisjoint : Disjoint first second)",
              "    (hOne : OneChangeOn χ (first ∪ second))",
              "    (hnormal : IsShortFirstMixedOmissionNormalForm567 first second witnesses ∨",
              "      IsShortSecondMixedOmissionNormalForm567 first second witnesses) :",
              "    ContainsTarget567 χ (first ∪ second) :=",
              "  mixedCarrierOnlyOmissionNormalForm_forces_target567_of_finite",
              "    mixed567AllOrderFiniteTheorem hsystem hfirstCard hsecondCard",
              "      hcarrierDisjoint hOne hnormal", "", "end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def generate_semantic_lean(vars_path: Path, core_dir: Path, lean_dir: Path,
                           chunk_size: int) -> dict[str, object]:
    by_variable, clauses, origins = semantic_data(vars_path, core_dir)
    (lean_dir / "Mixed567AllOrderAtoms.lean").write_text(atoms_text(by_variable))
    chunk_count = (len(clauses) + chunk_size - 1) // chunk_size
    for index in range(chunk_count):
        start = index * chunk_size
        stop = min(start + chunk_size, len(clauses))
        (lean_dir / f"Mixed567AllOrderSemanticChunk{index:03d}.lean").write_text(
            chunk_text(index, start, stop, clauses, origins, by_variable))
    ranges = tree_ranges(len(clauses), 4)
    for index, (start, stop) in enumerate(ranges):
        (lean_dir / f"Mixed567AllOrderSemanticElim{index:03d}.lean").write_text(
            eliminator_text(index, start, stop, chunk_size, clauses, origins))
    (lean_dir / "Mixed567AllOrder.lean").write_text(final_text(clauses, ranges, by_variable))
    return {"variables": len(by_variable), "clauses": len(clauses),
            "chunks": chunk_count, "eliminators": len(ranges)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--lrat", type=Path, required=True)
    parser.add_argument("--origins", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--vars", type=Path)
    parser.add_argument("--lean-dir", type=Path, default=Path("ErdosSzekeres"))
    parser.add_argument("--semantic-chunk-size", type=int, default=256)
    args = parser.parse_args()
    actual = {name: sha256(getattr(args, name)) for name in EXPECTED}
    if actual != EXPECTED:
        raise ValueError(f"frozen input hash mismatch: {actual}")
    variables, clauses = parse_cnf(args.cnf)
    additions = parse_lrat(args.lrat, len(clauses))
    summary = write_core(variables, clauses, additions, args.origins, args.output_dir)
    if args.vars is not None:
        summary["semantic_lean"] = generate_semantic_lean(
            args.vars, args.output_dir, args.lean_dir, args.semantic_chunk_size)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
