#!/usr/bin/env python3
"""Generate the exact Fin10 singleton-fan LRAT and Lean semantic bridge."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


SOURCE_REL = Path(
    "runs/agents/20260811-four-slot-structural-round/half-pure-singleton-k6n10"
)
RUN_REL = Path("runs/agents/20260811-four-slot-deep-wave/half-pure-fin10")
EXPECTED = {
    "formula.cnf": "a431ba8eb4c75796195c549e0fb6ad55b5deff369df257bb66ad852e399db575",
    "primary.lrat": "2d1390687db1ca7c205ddab3cb7589e889078055ad2c5d8570bb316cebdfc2c1",
    "encoding.json": "315fb0df5b88e9c01f8a6ea736ea8702b8c1c3c910b38fb9d2cfbdf7fecd19b8",
}
N = 10
TRIPLES = tuple(itertools.combinations(range(N), 3))
QUADS = tuple(itertools.combinations(range(N), 4))
FIVES = tuple(itertools.combinations(range(N), 5))
SIXES = tuple(itertools.combinations(range(N), 6))
TVAR = {triple: index + 1 for index, triple in enumerate(TRIPLES)}
QVAR = {quad: 121 + index for index, quad in enumerate(QUADS)}
FVAR = {five: 331 + index for index, five in enumerate(FIVES)}
LBAD = {five: 583 + index for index, five in enumerate(FIVES)}
UBAD = {five: 835 + index for index, five in enumerate(FIVES)}
CHUNK_SIZE = 32


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_frozen(source: Path, name: str) -> bytes:
    data = (source / name).read_bytes()
    if digest(data) != EXPECTED[name]:
        raise ValueError(f"frozen input hash mismatch: {name}")
    return data


def parse_dimacs(data: bytes):
    variables = expected = None
    clauses = []
    for line in data.decode().splitlines():
        if not line or line.startswith("c"):
            continue
        fields = line.split()
        if fields[0] == "p":
            _, kind, variables_text, expected_text = fields
            if kind != "cnf":
                raise ValueError("not CNF")
            variables, expected = int(variables_text), int(expected_text)
            continue
        values = tuple(map(int, fields))
        if not values or values[-1] != 0:
            raise ValueError("unterminated DIMACS clause")
        clauses.append(values[:-1])
    if variables is None or len(clauses) != expected:
        raise ValueError("bad DIMACS header")
    return variables, tuple(clauses)


def parse_lrat(data: bytes):
    additions = {}
    deletion_count = 0
    for line in data.decode().splitlines():
        fields = line.split()
        if not fields:
            continue
        if fields[1] == "d":
            if fields[-1] != "0":
                raise ValueError("unterminated deletion")
            deletion_count += 1
            continue
        old_id = int(fields[0])
        separator = fields.index("0", 1)
        clause = tuple(map(int, fields[1:separator]))
        hints = tuple(map(int, fields[separator + 1:-1]))
        if fields[-1] != "0" or any(hint <= 0 for hint in hints):
            raise ValueError("proof is not positive-hint LRAT")
        additions[old_id] = (clause, hints)
    return additions, deletion_count


def quad_triples(quad):
    a, b, c, d = quad
    return ((a, b, c), (a, b, d), (a, c, d), (b, c, d))


def blocker(variables, bits):
    return tuple(-variable if bit else variable for variable, bit in zip(variables, bits))


def strong_quad(bits):
    return bits[0] == bits[1] and bits[2] == bits[3]


def candidate_sides():
    for pivot in range(N):
        remaining = tuple(vertex for vertex in range(N) if vertex != pivot)
        for size in range(5, N):
            for side in itertools.combinations(remaining, size):
                yield pivot, side


def deep_literals(side: frozenset[int], pivot: int, lower: bool):
    for u, v in itertools.combinations(sorted(side), 2):
        triple = tuple(sorted((u, v, pivot)))
        required_left = triple[1] in side if lower else triple[1] == pivot
        yield -TVAR[triple] if required_left else TVAR[triple]


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
        variables = tuple(TVAR[t] for t in quad_triples(quad))
        for bits in itertools.product((False, True), repeat=4):
            if sum(a != b for a, b in zip(bits, bits[1:])) > 1:
                add("one_change", blocker(variables, bits), {"quad": quad})
        for bits in itertools.product((False, True), repeat=4):
            add("strong_quad_truth_table", blocker(variables, bits) +
                ((QVAR[quad] if strong_quad(bits) else -QVAR[quad]),), {"quad": quad})
    for five in FIVES:
        qvars = [QVAR[q] for q in itertools.combinations(five, 4)]
        for variable in qvars:
            add("strong_five_definition", (-FVAR[five], variable), {"five": five})
        add("strong_five_definition", (FVAR[five], *(-x for x in qvars)), {"five": five})
        tvars = [TVAR[t] for t in itertools.combinations(five, 3)]
        add("cup_bad_definition", (-LBAD[five], FVAR[five]), {"five": five})
        add("cup_bad_definition", (-LBAD[five], *(-x for x in tvars)), {"five": five})
        for variable in tvars:
            add("cup_bad_definition", (-FVAR[five], variable, LBAD[five]), {"five": five})
        add("cap_bad_definition", (-UBAD[five], FVAR[five]), {"five": five})
        add("cap_bad_definition", (-UBAD[five], *tvars), {"five": five})
        for variable in tvars:
            add("cap_bad_definition", (-FVAR[five], -variable, UBAD[five]), {"five": five})
    for six in SIXES:
        add("no_strong_six", tuple(-QVAR[q] for q in itertools.combinations(six, 4)),
            {"six": six})
    for pivot, side_tuple in candidate_sides():
        side = frozenset(side_tuple)
        for lower, badmap, category in (
            (True, LBAD, "lower_no_witness"),
            (False, UBAD, "upper_no_witness"),
        ):
            clause = list(deep_literals(side, pivot, lower))
            clause.extend(badmap[five] for five in itertools.combinations(side_tuple, 5))
            add(category, tuple(clause), {"pivot": pivot, "side": side_tuple, "lower": lower})
    return tuple(entries)


def dense_core(formula_data: bytes, proof_data: bytes):
    variable_count, clauses = parse_dimacs(formula_data)
    entries = annotated_formula()
    if variable_count != 1086 or len(clauses) != 17930:
        raise ValueError("unexpected full CNF dimensions")
    if tuple(entry["literals"] for entry in entries) != clauses:
        raise ValueError("semantic reconstruction differs from frozen CNF")
    additions, deletion_count = parse_lrat(proof_data)
    final_id = max(additions)
    if additions[final_id][0]:
        raise ValueError("final LRAT clause is not empty")
    needed_additions = {final_id}
    needed_initial = set()
    stack = [final_id]
    while stack:
        clause_id = stack.pop()
        for hint in additions[clause_id][1]:
            if hint <= len(clauses):
                needed_initial.add(hint)
            elif hint not in needed_additions:
                if hint not in additions:
                    raise ValueError(f"missing LRAT dependency {hint}")
                needed_additions.add(hint)
                stack.append(hint)
    base_ids = tuple(sorted(needed_initial))
    addition_ids = tuple(sorted(needed_additions))
    used_variables = tuple(sorted({abs(literal) for old in base_ids for literal in clauses[old - 1]}))
    if (len(base_ids), len(addition_ids), len(used_variables), deletion_count) != (2405, 2007, 438, 4730):
        raise ValueError("unexpected transitive core dimensions")
    variable_map = {old: new for new, old in enumerate(used_variables, 1)}
    clause_map = {old: new for new, old in enumerate(base_ids, 1)}
    for old in addition_ids:
        clause_map[old] = len(clause_map) + 1

    def remap_clause(clause):
        return tuple((1 if literal > 0 else -1) * variable_map[abs(literal)] for literal in clause)

    cnf_lines = [f"p cnf {len(used_variables)} {len(base_ids)}"]
    cnf_lines.extend(" ".join(map(str, remap_clause(clauses[old - 1]))) + " 0"
                     for old in base_ids)
    lrat_lines = []
    for old in addition_ids:
        clause, hints = additions[old]
        if any(hint not in clause_map for hint in hints):
            raise ValueError(f"unmapped LRAT hint for {old}")
        row = [str(clause_map[old]), *(map(str, remap_clause(clause))), "0",
               *(str(clause_map[hint]) for hint in hints), "0"]
        lrat_lines.append(" ".join(row))
    return {
        "core_cnf": ("\n".join(cnf_lines) + "\n").encode(),
        "core_lrat": ("\n".join(lrat_lines) + "\n").encode(),
        "entries": tuple(entries[old - 1] for old in base_ids),
        "used_variables": used_variables,
        "base_ids": base_ids,
        "addition_ids": addition_ids,
    }


def finset(vertices) -> str:
    return "{" + ", ".join(map(str, vertices)) + "}"


def atom_name(variable: int) -> str:
    return f"HalfPureSingletonFanFin10Atom{variable:04d}"


def atom_term(variable: int) -> str:
    return f"{atom_name(variable)} χ"


def triple_term(triple) -> str:
    a, b, c = triple
    return f"χ ⟨{a}, {b}, {c}, by decide, by decide⟩"


def strong_quad_term(quad) -> str:
    a, b, c, d = quad
    return f"HalfPureSingletonFanFin10StrongQuad χ {a} {b} {c} {d} " \
        "(by decide) (by decide) (by decide)"


def header(import_name: str) -> list[str]:
    return [
        "module", "", f"public import {import_name}", "", "@[expose] public section", "",
        "set_option maxHeartbeats 0", "set_option maxRecDepth 30000",
        "set_option linter.unusedSimpArgs false", "", "namespace ErdosSzekeres", "",
    ]


def conclusion_lines() -> list[str]:
    return [
        "/-- The exact bounded singleton-fan conclusion certified at Fin 10. -/",
        "def HalfPureSingletonFanFin10Conclusion (χ : TripleColoring 10) : Prop :=",
        "  ∃ side : Finset (Fin 10), ∃ pivot : Fin 10,",
        "    pivot ∉ side ∧", "    10 ≤ 2 * side.card ∧",
        "    ((HasDeepBelowSplit χ side {pivot} ∧",
        "        ∀ polygon : Finset (Fin 10),",
        "          polygon ⊆ side → polygon.card = 5 →",
        "            IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨",
        "     (HasDeepBelowSplit χ {pivot} side ∧",
        "        ∀ polygon : Finset (Fin 10),",
        "          polygon ⊆ side → polygon.card = 5 →",
        "            IsStrongPolygonSet χ polygon → IsCapSet χ polygon))", "",
        "def HalfPureSingletonFanFin10StrongQuad (χ : TripleColoring 10)",
        "    (a b c d : Fin 10) (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=",
        "  χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧",
        "    χ ⟨a, c, d, hab.trans hbc, hcd⟩ = χ ⟨b, c, d, hbc, hcd⟩", "",
    ]


def strong_set_iff_lines(vertices) -> list[str]:
    name = "halfPureSingletonFanFin10_strongSet_iff_mask" + f"{sum(1 << v for v in vertices):04d}"
    quads = tuple(itertools.combinations(vertices, 4))
    lines = [f"theorem {name} (χ : TripleColoring 10) :",
             f"    IsStrongPolygonSet χ {finset(vertices)} ↔"]
    for index, quad in enumerate(quads):
        suffix = " ∧" if index + 1 < len(quads) else " := by"
        lines.append(f"      {strong_quad_term(quad)}{suffix}")
    lines += ["  constructor", "  · intro h", "    refine ⟨" + ", ".join("?_" for _ in quads) + "⟩"]
    for quad in quads:
        a, b, c, d = quad
        lines += [f"    · simpa [HalfPureSingletonFanFin10StrongQuad] using h",
                  f"        (i := {a}) (j := {b}) (k := {c}) (l := {d})",
                  "        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)"]
    facts = ", ".join(f"h{i}" for i in range(len(quads)))
    choices = " | ".join("rfl" for _ in vertices)
    lines += [f"  · rintro ⟨{facts}⟩ i j k l hij hjk hkl hi hj hk hl",
              "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl",
              f"    rcases hi with {choices} <;>", f"      rcases hj with {choices} <;>",
              f"      rcases hk with {choices} <;>", f"      rcases hl with {choices} <;> try omega",
              "    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]", ""]
    return lines


def pure_set_iff_lines(five, cup: bool) -> list[str]:
    mask = sum(1 << v for v in five)
    kind = "cup" if cup else "cap"
    predicate = "IsCupSet" if cup else "IsCapSet"
    turn = "left" if cup else "right"
    triples = tuple(itertools.combinations(five, 3))
    lines = [f"theorem halfPureSingletonFanFin10_{kind}Set_iff_mask{mask:04d}",
             "    (χ : TripleColoring 10) :", f"    {predicate} χ {finset(five)} ↔"]
    for index, triple in enumerate(triples):
        suffix = " ∧" if index + 1 < len(triples) else " := by"
        lines.append(f"      {triple_term(triple)} = Turn.{turn}{suffix}")
    lines += ["  constructor", "  · intro h", "    exact ⟨"]
    for index in range(len(triples)):
        suffix = "," if index + 1 < len(triples) else "⟩"
        lines.append(f"      h _ (by simp) (by simp) (by simp){suffix}")
    facts = ", ".join(f"h{i}" for i in range(len(triples)))
    choices = " | ".join("rfl" for _ in five)
    lines += [f"  · rintro ⟨{facts}⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk",
              "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk",
              f"    rcases hi with {choices} <;>", f"      rcases hj with {choices} <;>",
              f"      rcases hk with {choices} <;> try omega", ""]
    return lines


def encoding_text(core) -> str:
    entries, used = core["entries"], core["used_variables"]
    lines = header("ErdosSzekeres.HalfPureSingletonFan") + conclusion_lines()
    for variable in used:
        lines.append(f"def {atom_name(variable)} (χ : TripleColoring 10) : Prop :=")
        if variable <= 120:
            lines.append(f"  {triple_term(TRIPLES[variable - 1])} = Turn.left")
        elif variable <= 330:
            lines.append(f"  {strong_quad_term(QUADS[variable - 121])}")
        elif variable <= 582:
            lines.append(f"  IsStrongPolygonSet χ {finset(FIVES[variable - 331])}")
        elif variable <= 834:
            five = FIVES[variable - 583]
            lines += [f"  IsStrongPolygonSet χ {finset(five)} ∧", f"    ¬IsCupSet χ {finset(five)}"]
        else:
            five = FIVES[variable - 835]
            lines += [f"  IsStrongPolygonSet χ {finset(five)} ∧", f"    ¬IsCapSet χ {finset(five)}"]
        lines.append("")
    strong_fives, cup_fives, cap_fives, strong_sixes, branch_sides = set(), set(), set(), set(), set()
    for entry in entries:
        category, origin = entry["category"], entry["origin"]
        if "five" in origin:
            strong_fives.add(origin["five"])
            if category == "cup_bad_definition": cup_fives.add(origin["five"])
            if category == "cap_bad_definition": cap_fives.add(origin["five"])
        if category == "no_strong_six": strong_sixes.add(origin["six"])
        if category.endswith("no_witness"): branch_sides.add(origin["side"])
    for five in sorted(strong_fives):
        lines += strong_set_iff_lines(five)
    for five in sorted(cup_fives):
        lines += pure_set_iff_lines(five, True)
    for five in sorted(cap_fives):
        lines += pure_set_iff_lines(five, False)
    for side in sorted(branch_sides):
        mask = sum(1 << v for v in side)
        lines += [f"theorem halfPureSingletonFanFin10_fiveSubset_eq_mask{mask:04d} :",
                  f"    ∀ polygon : Finset (Fin 10), polygon ⊆ {finset(side)} →",
                  f"      polygon.card = 5 → polygon = {finset(side)} := by decide", ""]
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def failure_expression(literals) -> str:
    return " ∧\n      ".join((f"¬{atom_term(abs(x))}" if x > 0 else atom_term(abs(x)))
                             for x in literals)


def unfold_lines(literals, target="at hbad") -> list[str]:
    names = [atom_name(v) for v in sorted({abs(x) for x in literals})]
    rows = ["  unfold " + names[0]]
    for name in names[1:]:
        if len(rows[-1]) + len(name) + 1 < 96:
            rows[-1] += " " + name
        else:
            rows.append("    " + name)
    rows[-1] += " " + target
    return rows


def color_cases(quad) -> list[str]:
    lines = []
    for index, triple in enumerate(quad_triples(quad)):
        lines.append("  " + "  " * index + f"cases hcolor{index} : {triple_term(triple)} <;>")
    lines.append("          simp_all [TurnSequenceAllowed, HalfPureSingletonFanFin10StrongQuad]")
    return lines


def clause_lemma(entry) -> list[str]:
    clause_id, category, origin = entry["id"], entry["category"], entry["origin"]
    lines = [f"theorem halfPureSingletonFanFin10_clause{clause_id:05d} (χ : TripleColoring 10)"]
    if category == "one_change":
        a, b, c, d = origin["quad"]
        lines += ["    (hone : OneChangeOn χ Finset.univ) :",
                  f"    ¬({failure_expression(entry['literals'])}) := by", "  intro hbad",
                  f"  have hallowed := hone (i := {a}) (j := {b}) (k := {c}) (l := {d})",
                  "    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)"]
        lines += unfold_lines(entry["literals"]) + color_cases(origin["quad"])
    elif category == "strong_quad_truth_table":
        lines += [f"    : ¬({failure_expression(entry['literals'])}) := by", "  intro hbad"]
        lines += unfold_lines(entry["literals"]) + color_cases(origin["quad"])
    elif category in {"strong_five_definition", "cup_bad_definition", "cap_bad_definition"}:
        five = origin["five"]
        mask = sum(1 << v for v in five)
        lines += [f"    : ¬({failure_expression(entry['literals'])}) := by", "  intro hbad"]
        lines += unfold_lines(entry["literals"])
        simp_names = [f"halfPureSingletonFanFin10_strongSet_iff_mask{mask:04d}"]
        if category == "cup_bad_definition":
            simp_names.append(f"halfPureSingletonFanFin10_cupSet_iff_mask{mask:04d}")
        if category == "cap_bad_definition":
            simp_names.append(f"halfPureSingletonFanFin10_capSet_iff_mask{mask:04d}")
        lines.append("  simp only [" + ", ".join(simp_names) + "] at hbad")
        if category == "strong_five_definition":
            lines.append("  tauto")
        else:
            for index, triple in enumerate(itertools.combinations(five, 3)):
                lines.append("  " + "  " * index +
                             f"cases hcolor{index} : {triple_term(triple)} <;>")
            lines.append("                      simp_all [HalfPureSingletonFanFin10StrongQuad]")
    elif category == "no_strong_six":
        six = origin["six"]
        choices = " | ".join("rfl" for _ in six)
        lines += ["    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :",
                  f"    ¬({failure_expression(entry['literals'])}) := by", "  intro hbad",
                  f"  have hnot : ¬IsStrongPolygonSet χ {finset(six)} := by",
                  "    intro hstrong", f"    exact hnoStrong ⟨{finset(six)}, by simp, by decide, hstrong⟩",
                  "  apply hnot", "  intro i j k l hij hjk hkl hi hj hk hl",
                  "  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl"]
        lines += unfold_lines(entry["literals"])
        lines += [f"  rcases hi with {choices} <;>", f"    rcases hj with {choices} <;>",
                  f"    rcases hk with {choices} <;>", f"    rcases hl with {choices} <;> try omega",
                  "  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]"]
    else:
        side, pivot, lower = origin["side"], origin["pivot"], origin["lower"]
        if len(side) != 5 or len(entry["literals"]) != 11:
            raise ValueError(f"retained branch {clause_id} is not an exact five-plus-one leaf")
        facts = ", ".join(f"h{i}" for i in range(11))
        branch = "Or.inl" if lower else "Or.inr"
        pure = "IsCupSet" if lower else "IsCapSet"
        first = side if lower else (pivot,)
        second = (pivot,) if lower else side
        union = tuple(sorted((*side, pivot)))
        choices = " | ".join("rfl" for _ in union)
        mask = sum(1 << v for v in side)
        lines += ["    (hno : ¬HalfPureSingletonFanFin10Conclusion χ) :",
                  f"    ¬({failure_expression(entry['literals'])}) := by", f"  rintro ⟨{facts}⟩"]
        for index, literal in enumerate(entry["literals"]):
            lines.append(f"  unfold {atom_name(abs(literal))} at h{index}")
        lines += ["  apply hno", "  unfold HalfPureSingletonFanFin10Conclusion",
                  f"  refine ⟨{finset(side)}, {pivot}, by decide, by decide, {branch} ?_⟩",
                  "  refine ⟨?_, ?_⟩", "  · refine ⟨by decide, ?_⟩",
                  "    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper",
                  "    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk",
                  f"    rcases hi with {choices} <;>", f"      rcases hj with {choices} <;>",
                  f"      rcases hk with {choices} <;> try omega",
                  "    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all",
                  "  · intro polygon hsub hcard hstrong",
                  f"    have heq := halfPureSingletonFanFin10_fiveSubset_eq_mask{mask:04d}",
                  "      polygon hsub hcard", "    subst polygon", f"    show {pure} χ {finset(side)}",
                  "    by_contra hnotPure", "    apply h10", "    exact ⟨hstrong, hnotPure⟩"]
    return lines


def clause_chunk_text(index: int, entries) -> str:
    lines = header("ErdosSzekeres.HalfPureSingletonFanFin10Encoding")
    lines += [f"/-! Semantic clauses for retained Fin10 LRAT leaf chunk {index}. -/", ""]
    for entry in entries:
        lines += clause_lemma(entry) + [""]
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def unsat_text() -> str:
    stem = "../certificates/half-pure-singleton-fin10/half-pure-singleton-fin10-core"
    return f'''module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

namespace ErdosSzekeres

lrat_proof halfPureSingletonFanFin10_lrat_unsat
  (include_str "{stem}.cnf")
  (include_str "{stem}.lrat")

end ErdosSzekeres

end
'''


def final_text(core, chunk_count: int) -> str:
    lines = ["module", "", "public import ErdosSzekeres.HalfPureSingletonFanFin10Unsat"]
    lines += [f"public import ErdosSzekeres.HalfPureSingletonFanFin10ClauseChunk{i:02d}"
              for i in range(chunk_count)]
    lines += ["", "@[expose] public section", "", "set_option maxHeartbeats 0",
              "set_option maxRecDepth 30000", "set_option linter.unusedSimpArgs false", "",
              "namespace ErdosSzekeres", "",
              "/-- The exact nonvacuous Fin10 singleton-fan certificate conclusion. -/",
              "theorem halfPureSingletonFanFin10Conclusion_of_oneChange",
              "    (χ : TripleColoring 10)", "    (hone : OneChangeOn χ Finset.univ)",
              "    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :",
              "    HalfPureSingletonFanFin10Conclusion χ := by", "  by_contra hno",
              "  have hbad := halfPureSingletonFanFin10_lrat_unsat"]
    atoms = [f"({atom_term(variable)})" for variable in core["used_variables"]]
    for start in range(0, len(atoms), 5):
        lines.append("    " + " ".join(atoms[start:start + 5]))
    lines.append("  simp only [")
    for entry in core["entries"]:
        lemma = f"halfPureSingletonFanFin10_clause{entry['id']:05d} χ"
        if entry["category"] == "one_change": lemma += " hone"
        elif entry["category"] == "no_strong_six": lemma += " hnoStrong"
        elif entry["category"].endswith("no_witness"): lemma += " hno"
        lines.append(f"    {lemma},")
    lines += ["    false_or, or_false", "  ] at hbad", "",
              "/-- Exact k=6,n=10 singleton-fan theorem under the rank-three one-change law. -/",
              "theorem halfPureSingletonFanAtSixFinTen_of_oneChange",
              "    (χ : TripleColoring 10)", "    (hone : OneChangeOn χ Finset.univ)",
              "    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :",
              "    ∃ side : Finset (Fin 10), ∃ pivot : Fin 10,", "      pivot ∉ side ∧",
              "      10 ≤ 2 * side.card ∧", "      ((HasDeepBelowSplit χ side {pivot} ∧",
              "          ∀ polygon : Finset (Fin 10),",
              "            polygon ⊆ side → polygon.card = 5 →",
              "              IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨",
              "       (HasDeepBelowSplit χ {pivot} side ∧",
              "          ∀ polygon : Finset (Fin 10),",
              "            polygon ⊆ side → polygon.card = 5 →",
              "              IsStrongPolygonSet χ polygon → IsCapSet χ polygon)) := by",
              "  simpa only [HalfPureSingletonFanFin10Conclusion] using",
              "    halfPureSingletonFanFin10Conclusion_of_oneChange χ hone hnoStrong", "",
              "end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def generated_outputs(repo: Path):
    source = repo / SOURCE_REL
    formula = read_frozen(source, "formula.cnf")
    proof = read_frozen(source, "primary.lrat")
    metadata = json.loads(read_frozen(source, "encoding.json"))
    if metadata["variable_count"] != 1086 or metadata["clause_count"] != 17930:
        raise ValueError("frozen metadata dimensions changed")
    core = dense_core(formula, proof)
    chunks = [core["entries"][start:start + CHUNK_SIZE]
              for start in range(0, len(core["entries"]), CHUNK_SIZE)]
    outputs = {
        RUN_REL / "half-pure-singleton-fin10-core.cnf": core["core_cnf"],
        RUN_REL / "half-pure-singleton-fin10-core.lrat": core["core_lrat"],
        Path("ErdosSzekeres/HalfPureSingletonFanFin10Encoding.lean"):
            encoding_text(core).encode(),
        Path("ErdosSzekeres/HalfPureSingletonFanFin10Unsat.lean"): unsat_text().encode(),
        Path("ErdosSzekeres/HalfPureSingletonFanFin10.lean"):
            final_text(core, len(chunks)).encode(),
    }
    for index, chunk in enumerate(chunks):
        outputs[Path(f"ErdosSzekeres/HalfPureSingletonFanFin10ClauseChunk{index:02d}.lean")] = (
            clause_chunk_text(index, chunk).encode()
        )
    summary = {
        "schema_version": 1, "source_cnf_sha256": EXPECTED["formula.cnf"],
        "source_lrat_sha256": EXPECTED["primary.lrat"], "source_variables": 1086,
        "source_clauses": 17930, "source_additions": 6502,
        "core_variables": len(core["used_variables"]), "core_clauses": len(core["base_ids"]),
        "core_additions": len(core["addition_ids"]), "chunk_count": len(chunks),
    }
    outputs[RUN_REL / "generation-summary.json"] = (
        json.dumps(summary, indent=2, sort_keys=True) + "\n").encode()
    return outputs


def generate(repo: Path, output_root: Path) -> dict[str, str]:
    outputs = generated_outputs(repo)
    for relative, data in outputs.items():
        path = output_root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return {str(path): digest(data) for path, data in sorted(outputs.items())}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--output-root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    print(json.dumps(generate(args.repo.resolve(), args.output_root.resolve()), indent=2,
                     sort_keys=True))


if __name__ == "__main__":
    main()
