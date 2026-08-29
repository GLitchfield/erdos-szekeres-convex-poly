#!/usr/bin/env python3
"""Generate the Lean semantic reflection of the compact Fin13 LRAT core.

The SAT encoding has three kinds of atoms: triple colors, strong quadruples,
and strong five-sets.  This generator freezes the dependency core, assigns
each retained Boolean variable its mathematical meaning, proves every retained
base clause from the one-change/no-strong-six hypotheses (or from the negation
of the desired seven-point support), and specializes the kernel-checked LRAT
refutation to those meanings.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from generate_predecessor_half_fin13_tseitin_sat import (
    FIVES,
    FVAR,
    QUADS,
    QVAR,
    TRIPLES,
    TVAR,
    annotated_formula,
    quad_triples,
)


RUN_REL = Path("runs/experiments/20260826-predecessor-half-fin13")
CORE_REL = RUN_REL / "compact-core"
EXPECTED = {
    RUN_REL / "compact.cnf":
        "a2cacd1fc2b19cf29d0aa2a3a5acb21a0547c66e52be4112ad59dbb44822ecaa",
    CORE_REL / "core.cnf":
        "56e0d0a80c51379052ed70c77c15305e4788be597f50a05c6614dbdb0ebbb86c",
    CORE_REL / "core.lrat":
        "a1d524ee83706eff3a8560e41825a01d03be47eb47c3c9fa5014ddde061fbd5d",
    CORE_REL / "core-map.json":
        "056a06aaacf278991758bce7872f2f12e6e5f0b17fc7d8b37519c7d2774b992c",
}
SUPPORT_CHUNK_SIZE = 40
CLAUSE_CHUNK_SIZE = 128
SEMANTIC_SEGMENT_DEPTH = 7

TRIPLE_BY_VAR = {variable: triple for triple, variable in TVAR.items()}
QUAD_BY_VAR = {variable: quad for quad, variable in QVAR.items()}
FIVE_BY_VAR = {variable: five for five, variable in FVAR.items()}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_frozen(repo: Path, relative: Path) -> bytes:
    data = (repo / relative).read_bytes()
    if digest(data) != EXPECTED[relative]:
        raise ValueError(f"frozen input hash mismatch: {relative}")
    return data


def parse_cnf(data: bytes) -> tuple[int, tuple[tuple[int, ...], ...]]:
    variables = expected = None
    clauses: list[tuple[int, ...]] = []
    for raw in data.decode().splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        fields = line.split()
        if fields[0] == "p":
            _, kind, variable_text, clause_text = fields
            if kind != "cnf":
                raise ValueError("expected DIMACS CNF")
            variables = int(variable_text)
            expected = int(clause_text)
            continue
        values = tuple(map(int, fields))
        if not values or values[-1] != 0:
            raise ValueError("unterminated DIMACS clause")
        clauses.append(values[:-1])
    if variables is None or expected != len(clauses):
        raise ValueError("DIMACS header mismatch")
    return variables, tuple(clauses)


def load_core(repo: Path) -> dict[str, object]:
    compact = read_frozen(repo, RUN_REL / "compact.cnf")
    read_frozen(repo, CORE_REL / "core.cnf")
    read_frozen(repo, CORE_REL / "core.lrat")
    metadata = json.loads(read_frozen(repo, CORE_REL / "core-map.json"))
    variables, clauses = parse_cnf(compact)
    entries = annotated_formula()
    if variables != 2288 or len(clauses) != 28314:
        raise ValueError("unexpected compact formula dimensions")
    if tuple(entry["literals"] for entry in entries) != clauses:
        raise ValueError("semantic reconstruction differs from frozen compact CNF")
    base_ids = tuple(metadata["selected_base_ids"])
    used_variables = tuple(sorted(map(int, metadata["variable_map_old_to_new"])))
    variable_map = {
        int(old): int(new)
        for old, new in metadata["variable_map_old_to_new"].items()
    }
    if [variable_map[old] for old in used_variables] != list(
        range(1, len(used_variables) + 1)
    ):
        raise ValueError("core variable map is not the expected dense order")
    selected = tuple(entries[clause_id - 1] for clause_id in base_ids)
    if (len(base_ids), len(used_variables)) != (12585, 1332):
        raise ValueError("unexpected dependency-core dimensions")
    return {
        "entries": selected,
        "base_ids": base_ids,
        "used_variables": used_variables,
    }


def finset(vertices: tuple[int, ...]) -> str:
    return "{" + ", ".join(map(str, vertices)) + "}"


def mask(vertices: tuple[int, ...]) -> int:
    return sum(1 << vertex for vertex in vertices)


def atom_name(variable: int) -> str:
    return f"PredecessorHalfFin13Atom{variable:04d}"


def atom_term(variable: int) -> str:
    return f"{atom_name(variable)} chi"


def triple_term(triple: tuple[int, int, int]) -> str:
    a, b, c = triple
    return f"chi ⟨{a}, {b}, {c}, by decide, by decide⟩"


def strong_quad_term(quad: tuple[int, int, int, int]) -> str:
    a, b, c, d = quad
    return (
        f"PredecessorHalfFin13StrongQuad chi {a} {b} {c} {d} "
        "(by decide) (by decide) (by decide)"
    )


def header(imports: list[str]) -> list[str]:
    lines = ["module", ""]
    lines += [f"public import {name}" for name in imports]
    lines += [
        "",
        "@[expose] public section",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 30000",
        "set_option linter.unusedSimpArgs false",
        "",
        "namespace ErdosSzekeres",
        "",
    ]
    return lines


def footer() -> list[str]:
    return ["end ErdosSzekeres", "", "end", ""]


def encoding_text(core: dict[str, object]) -> str:
    lines = header(["ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport"])
    lines += [
        "/-- The exact Fin13 support conclusion certified by the LRAT core. -/",
        "def PredecessorHalfFin13Conclusion (chi : TripleColoring 13) : Prop :=",
        "  ∃ support : Finset (Fin 13),",
        "    support.card = 7 ∧",
        "    ¬ContainsStrongPolygonSet chi support 5",
        "",
        "/-- The two equalities contributed by one ordered quadruple to the",
        "strong-polygon predicate. -/",
        "def PredecessorHalfFin13StrongQuad (chi : TripleColoring 13)",
        "    (a b c d : Fin 13) (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=",
        "  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧",
        "    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩",
        "",
    ]
    for variable in core["used_variables"]:
        lines.append(f"def {atom_name(variable)} (chi : TripleColoring 13) : Prop :=")
        if variable in TRIPLE_BY_VAR:
            lines.append(f"  {triple_term(TRIPLE_BY_VAR[variable])} = Turn.left")
        elif variable in QUAD_BY_VAR:
            lines.append(f"  {strong_quad_term(QUAD_BY_VAR[variable])}")
        elif variable in FIVE_BY_VAR:
            lines.append(
                f"  IsStrongPolygonSet chi {finset(FIVE_BY_VAR[variable])}"
            )
        else:
            raise ValueError(f"unknown semantic variable {variable}")
        lines.append("")
    lines += footer()
    return "\n".join(lines)


def strong_set_iff_lines(five: tuple[int, ...]) -> list[str]:
    quads = tuple(itertools.combinations(five, 4))
    name = f"predecessorHalfFin13_strongSet_iff_mask{mask(five):04d}"
    lines = [
        f"theorem {name} (chi : TripleColoring 13) :",
        f"    IsStrongPolygonSet chi {finset(five)} ↔",
    ]
    for index, quad in enumerate(quads):
        suffix = " ∧" if index + 1 < len(quads) else " := by"
        lines.append(f"      {strong_quad_term(quad)}{suffix}")
    lines += [
        "  constructor",
        "  · intro h",
        "    refine ⟨" + ", ".join("?_" for _ in quads) + "⟩",
    ]
    for quad in quads:
        a, b, c, d = quad
        lines += [
            "    · simpa [PredecessorHalfFin13StrongQuad] using h",
            f"        (i := {a}) (j := {b}) (k := {c}) (l := {d})",
            "        (by decide) (by decide) (by decide)",
            "        (by simp) (by simp) (by simp) (by simp)",
        ]
    facts = ", ".join(f"h{index}" for index in range(len(quads)))
    choices = " | ".join("rfl" for _ in five)
    lines += [
        f"  · rintro ⟨{facts}⟩ i j k l hij hjk hkl hi hj hk hl",
        "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl",
        f"    rcases hi with {choices} <;>",
        f"      rcases hj with {choices} <;>",
        f"      rcases hk with {choices} <;>",
        f"      rcases hl with {choices} <;> try omega",
        "    all_goals simp_all [PredecessorHalfFin13StrongQuad]",
    ]
    return lines


def five_subset_lines(seven: tuple[int, ...]) -> list[str]:
    fives = tuple(itertools.combinations(seven, 5))
    name = f"predecessorHalfFin13_fiveSubset_mask{mask(seven):04d}"
    lines = [
        f"theorem {name} :",
        f"    ∀ polygon : Finset (Fin 13), polygon ⊆ {finset(seven)} →",
        "      polygon.card = 5 →",
    ]
    for index, five in enumerate(fives):
        suffix = " ∨" if index + 1 < len(fives) else " := by"
        lines.append(f"        polygon = {finset(five)}{suffix}")
    choices = " | ".join("rfl" for _ in seven)
    lines += [
        "  intro polygon hsubset hcard",
        f"  have hdiffcard : ({finset(seven)} \\ polygon).card = 2 := by",
        "    rw [Finset.card_sdiff_of_subset hsubset, hcard]",
        f"    have hsevenCard : ({finset(seven)} : Finset (Fin 13)).card = 7 := by decide",
        "    omega",
        "  obtain ⟨x, y, hxy, hdiff⟩ := Finset.card_eq_two.mp hdiffcard",
        f"  have hxDiff : x ∈ {finset(seven)} \\ polygon := by",
        "    rw [hdiff]",
        "    simp",
        f"  have hyDiff : y ∈ {finset(seven)} \\ polygon := by",
        "    rw [hdiff]",
        "    simp",
        f"  have hx : x ∈ ({finset(seven)} : Finset (Fin 13)) :=",
        "    (Finset.mem_sdiff.mp hxDiff).1",
        f"  have hy : y ∈ ({finset(seven)} : Finset (Fin 13)) :=",
        "    (Finset.mem_sdiff.mp hyDiff).1",
        f"  have heq : polygon = {finset(seven)} \\ {{x, y}} := by",
        "    calc",
        f"      polygon = {finset(seven)} \\ ({finset(seven)} \\ polygon) :=",
        "        (Finset.sdiff_sdiff_eq_self hsubset).symm",
        f"      _ = {finset(seven)} \\ {{x, y}} := by rw [hdiff]",
        "  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy",
        f"  rcases hx with {choices} <;>",
        f"    rcases hy with {choices} <;> simp_all <;> decide",
    ]
    return lines


def support_facts(core: dict[str, object]) -> tuple[list[tuple[str, tuple[int, ...]]], ...]:
    strong_fives = {
        tuple(entry["origin"]["five"])
        for entry in core["entries"]
        if entry["category"] == "strong_five_definition"
    }
    sevens = {
        tuple(entry["origin"]["seven"])
        for entry in core["entries"]
        if entry["category"] == "every_seven_has_strong_five"
    }
    facts = [("five", value) for value in sorted(strong_fives)]
    facts += [("seven", value) for value in sorted(sevens)]
    return tuple(facts)


def support_chunk_text(index: int, facts: tuple[tuple[str, tuple[int, ...]], ...]) -> str:
    lines = header(["ErdosSzekeres.PredecessorHalfFin13Encoding"])
    lines += [f"/-! Semantic helper facts in bounded group {index:03d}. -/", ""]
    for kind, vertices in facts:
        if kind == "five":
            lines += strong_set_iff_lines(vertices)
        else:
            lines += five_subset_lines(vertices)
        lines.append("")
    lines += footer()
    return "\n".join(lines)


def support_text(chunk_count: int) -> str:
    imports = [
        f"ErdosSzekeres.PredecessorHalfFin13SupportSegment{index:03d}"
        for index in range(chunk_count)
    ]
    return "\n".join(header(imports) + footer())


def failure_expression(literals: tuple[int, ...]) -> str:
    return " ∧\n      ".join(
        f"¬{atom_term(abs(literal))}" if literal > 0 else atom_term(abs(literal))
        for literal in literals
    )


def unfold_lines(literals: tuple[int, ...]) -> list[str]:
    names = [atom_name(value) for value in sorted({abs(item) for item in literals})]
    rows = ["  unfold " + names[0]]
    for name in names[1:]:
        if len(rows[-1]) + len(name) + 1 < 96:
            rows[-1] += " " + name
        else:
            rows.append("    " + name)
    rows[-1] += " at hbad"
    return rows


def color_cases(quad: tuple[int, int, int, int], *, one_change: bool) -> list[str]:
    lines: list[str] = []
    for index, triple in enumerate(quad_triples(quad)):
        lines.append(
            "  " + "  " * index
            + f"cases hcolor{index} : {triple_term(triple)} <;>"
        )
    simp = "TurnSequenceAllowed, " if one_change else ""
    lines.append(
        "          simp_all ["
        + simp
        + "PredecessorHalfFin13StrongQuad]"
    )
    return lines


def clause_lemma(entry: dict[str, object]) -> list[str]:
    clause_id = entry["id"]
    category = entry["category"]
    origin = entry["origin"]
    literals = entry["literals"]
    lines = [
        f"theorem predecessorHalfFin13_clause{clause_id:05d} (chi : TripleColoring 13)"
    ]
    if category == "one_change":
        a, b, c, d = origin["quad"]
        lines += [
            "    (hone : OneChangeOn chi Finset.univ) :",
            f"    ¬({failure_expression(literals)}) := by",
            "  intro hbad",
            f"  have hallowed := hone (i := {a}) (j := {b}) (k := {c}) (l := {d})",
            "    (by decide) (by decide) (by decide)",
            "    (by simp) (by simp) (by simp) (by simp)",
        ]
        lines += unfold_lines(literals)
        lines += color_cases(tuple(origin["quad"]), one_change=True)
    elif category == "strong_quad_definition":
        lines += [
            f"    : ¬({failure_expression(literals)}) := by",
            "  intro hbad",
        ]
        lines += unfold_lines(literals)
        lines += color_cases(tuple(origin["quad"]), one_change=False)
    elif category == "strong_five_definition":
        five = tuple(origin["five"])
        lines += [
            f"    : ¬({failure_expression(literals)}) := by",
            "  intro hbad",
        ]
        lines += unfold_lines(literals)
        lines += [
            "  simp only [",
            f"    predecessorHalfFin13_strongSet_iff_mask{mask(five):04d}",
            "  ] at hbad",
            "  tauto",
        ]
    elif category == "no_strong_six":
        six = tuple(origin["six"])
        choices = " | ".join("rfl" for _ in six)
        lines += [
            "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :",
            f"    ¬({failure_expression(literals)}) := by",
            "  intro hbad",
            f"  have hnot : ¬IsStrongPolygonSet chi {finset(six)} := by",
            "    intro hstrong",
            f"    exact hnoStrong ⟨{finset(six)}, by simp, by decide, hstrong⟩",
            "  apply hnot",
            "  intro i j k l hij hjk hkl hi hj hk hl",
            "  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl",
        ]
        lines += unfold_lines(literals)
        lines += [
            f"  rcases hi with {choices} <;>",
            f"    rcases hj with {choices} <;>",
            f"    rcases hk with {choices} <;>",
            f"    rcases hl with {choices} <;> try omega",
            "  all_goals simp_all [PredecessorHalfFin13StrongQuad]",
        ]
    elif category == "every_seven_has_strong_five":
        seven = tuple(origin["seven"])
        fives = tuple(itertools.combinations(seven, 5))
        choices = " | ".join(f"h{index}" for index in range(len(fives)))
        lines += [
            "    (hno : ¬PredecessorHalfFin13Conclusion chi) :",
            f"    ¬({failure_expression(literals)}) := by",
            "  intro hbad",
            "  apply hno",
            f"  refine ⟨{finset(seven)}, by decide, ?_⟩",
            "  rintro ⟨polygon, hsubset, hcard, hstrong⟩",
            f"  have heq := predecessorHalfFin13_fiveSubset_mask{mask(seven):04d}",
            "    polygon hsubset hcard",
        ]
        lines += unfold_lines(literals)
        lines += [
            f"  rcases heq with {choices} <;>",
            "    subst polygon <;> simp_all",
        ]
    else:
        raise ValueError(f"unknown clause category {category}")
    return lines


def clause_chunk_text(index: int, entries: tuple[dict[str, object], ...]) -> str:
    lines = header(["ErdosSzekeres.PredecessorHalfFin13Support"])
    lines += [f"/-! Retained Fin13 semantic clauses in bounded group {index:03d}. -/", ""]
    for entry in entries:
        lines += clause_lemma(entry)
        lines.append("")
    lines += footer()
    return "\n".join(lines)


def balanced_ranges(start: int, stop: int, depth: int) -> tuple[tuple[int, int], ...]:
    if depth == 0:
        return ((start, stop),)
    middle = start + (stop - start) // 2
    return (
        balanced_ranges(start, middle, depth - 1)
        + balanced_ranges(middle, stop, depth - 1)
    )


def balanced_failure_expression(entries: tuple[dict[str, object], ...]) -> str:
    if len(entries) == 1:
        return f"({failure_expression(entries[0]['literals'])})"
    middle = len(entries) // 2
    left = balanced_failure_expression(entries[:middle])
    right = balanced_failure_expression(entries[middle:])
    return f"({left} ∨\n      {right})"


def clause_application(entry: dict[str, object]) -> str:
    lemma = f"predecessorHalfFin13_clause{entry['id']:05d} chi"
    if entry["category"] == "one_change":
        lemma += " hone"
    elif entry["category"] == "no_strong_six":
        lemma += " hnoStrong"
    elif entry["category"] == "every_seven_has_strong_five":
        lemma += " hno"
    return lemma


def reject_tree_lines(entries: tuple[dict[str, object], ...], indent: str) -> list[str]:
    if len(entries) == 1:
        return [f"{indent}exact {clause_application(entries[0])} hbad"]
    middle = len(entries) // 2
    lines = [f"{indent}rcases hbad with hbad | hbad", f"{indent}·"]
    lines += reject_tree_lines(entries[:middle], indent + "  ")
    lines.append(f"{indent}·")
    lines += reject_tree_lines(entries[middle:], indent + "  ")
    return lines


def semantic_segment_text(
    index: int,
    entries: tuple[dict[str, object], ...],
    start: int,
    stop: int,
) -> str:
    first_chunk = start // CLAUSE_CHUNK_SIZE
    last_chunk = (stop - 1) // CLAUSE_CHUNK_SIZE
    imports = [
        f"ErdosSzekeres.PredecessorHalfFin13ClauseChunk{chunk:03d}"
        for chunk in range(first_chunk, last_chunk + 1)
    ]
    lines = header(imports)
    lines += [
        f"/-! Semantic rejection of balanced CNF subtree {index:03d}. -/",
        "",
        f"theorem predecessorHalfFin13_rejectSemanticSegment{index:03d}",
        "    (chi : TripleColoring 13)",
        "    (hone : OneChangeOn chi Finset.univ)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)",
        "    (hno : ¬PredecessorHalfFin13Conclusion chi) :",
        f"    ¬({balanced_failure_expression(entries)}) := by",
        "  intro hbad",
    ]
    lines += reject_tree_lines(entries, "  ")
    lines.append("")
    lines += footer()
    return "\n".join(lines)


def reject_segment_tree_lines(
    segments: tuple[tuple[int, int], ...], indent: str
) -> list[str]:
    if len(segments) == 1:
        index = segments[0][0]
        return [
            f"{indent}exact predecessorHalfFin13_rejectSemanticSegment{index:03d}",
            f"{indent}  chi hone hnoStrong hno hbad",
        ]
    middle = len(segments) // 2
    lines = [f"{indent}rcases hbad with hbad | hbad", f"{indent}·"]
    lines += reject_segment_tree_lines(segments[:middle], indent + "  ")
    lines.append(f"{indent}·")
    lines += reject_segment_tree_lines(segments[middle:], indent + "  ")
    return lines


def final_text(core: dict[str, object], semantic_segment_count: int) -> str:
    imports = ["ErdosSzekeres.PredecessorHalfFin13Unsat"]
    imports += [
        f"ErdosSzekeres.PredecessorHalfFin13SemanticSegment{index:03d}"
        for index in range(semantic_segment_count)
    ]
    lines = header(imports)
    lines += [
        "/-- Every one-change coloring on thirteen vertices without a strong",
        "six-set has a seven-point support without a strong five-set. -/",
        "theorem predecessorHalfFin13Conclusion_of_oneChange",
        "    (chi : TripleColoring 13)",
        "    (hone : OneChangeOn chi Finset.univ)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :",
        "    PredecessorHalfFin13Conclusion chi := by",
        "  by_contra hno",
        "  have hbad := predecessorHalfFin13_lrat_unsat",
    ]
    atoms = [f"({atom_term(variable)})" for variable in core["used_variables"]]
    for start in range(0, len(atoms), 4):
        lines.append("    " + " ".join(atoms[start:start + 4]))
    lines += [
        "  unfold PredecessorHalfFin13Checkpoint.bad at hbad",
    ]
    segment_indices = tuple((index, index) for index in range(semantic_segment_count))
    lines += reject_segment_tree_lines(segment_indices, "  ")
    lines += [
        "",
        "/-- Unpacked exact-seven Fin13 support theorem. -/",
        "theorem predecessorFreeSevenSubsetAtSixFinThirteen_of_oneChange",
        "    (chi : TripleColoring 13)",
        "    (hone : OneChangeOn chi Finset.univ)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :",
        "    ∃ support : Finset (Fin 13),",
        "      support.card = 7 ∧",
        "      ¬ContainsStrongPolygonSet chi support 5 := by",
        "  simpa only [PredecessorHalfFin13Conclusion] using",
        "    predecessorHalfFin13Conclusion_of_oneChange chi hone hnoStrong",
        "",
        "/-- Transport the Fin13 theorem through any increasing thirteen-point window. -/",
        "theorem predecessorFreeSevenSubsetAtSixFinThirteenWindow_of_oneChange",
        "    {n : Nat} (chi : TripleColoring n) (f : Fin 13 ↪o Fin n)",
        "    (hone : OneChangeOn chi (Finset.univ.image f))",
        "    (hnoStrong :",
        "      ¬ContainsStrongPolygonSet chi (Finset.univ.image f) 6) :",
        "    ∃ support : Finset (Fin n),",
        "      support ⊆ Finset.univ.image f ∧",
        "      support.card = 7 ∧",
        "      ¬ContainsStrongPolygonSet chi support 5 := by",
        "  have honeRestrict : OneChangeOn (chi.restrict f) Finset.univ := by",
        "    intro i j k l hij hjk hkl _ _ _ _",
        "    simpa [TripleColoring.restrict, OrderedTriple.map] using",
        "      hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)",
        "        (by simp) (by simp) (by simp) (by simp)",
        "  have hnoStrongRestrict :",
        "      ¬ContainsStrongPolygonSet (chi.restrict f) Finset.univ 6 := by",
        "    intro hstrong",
        "    exact hnoStrong",
        "      ((containsStrongPolygonSet_image_restrict_iff chi f Finset.univ).mp hstrong)",
        "  obtain ⟨support, hcard, hfree⟩ :=",
        "    predecessorFreeSevenSubsetAtSixFinThirteen_of_oneChange",
        "      (chi.restrict f) honeRestrict hnoStrongRestrict",
        "  refine ⟨support.image f,",
        "    Finset.image_mono f (Finset.subset_univ support), ?_, ?_⟩",
        "  · exact (Finset.card_image_of_injective support f.injective).trans hcard",
        "  · intro hstrong",
        "    exact hfree",
        "      ((containsStrongPolygonSet_image_restrict_iff chi f support).mpr hstrong)",
        "",
    ]
    lines += footer()
    return "\n".join(lines)


def generated_outputs(repo: Path) -> dict[Path, bytes]:
    core = load_core(repo)
    facts = support_facts(core)
    support_chunks = tuple(
        tuple(facts[start:start + SUPPORT_CHUNK_SIZE])
        for start in range(0, len(facts), SUPPORT_CHUNK_SIZE)
    )
    entries = core["entries"]
    clause_chunks = tuple(
        tuple(entries[start:start + CLAUSE_CHUNK_SIZE])
        for start in range(0, len(entries), CLAUSE_CHUNK_SIZE)
    )
    semantic_ranges = balanced_ranges(
        0, len(entries), SEMANTIC_SEGMENT_DEPTH
    )
    outputs: dict[Path, bytes] = {
        Path("ErdosSzekeres/PredecessorHalfFin13Encoding.lean"):
            encoding_text(core).encode(),
        Path("ErdosSzekeres/PredecessorHalfFin13Support.lean"):
            support_text(len(support_chunks)).encode(),
        Path("ErdosSzekeres/PredecessorHalfFin13.lean"):
            final_text(core, len(semantic_ranges)).encode(),
    }
    for index, chunk in enumerate(support_chunks):
        outputs[
            Path(f"ErdosSzekeres/PredecessorHalfFin13SupportSegment{index:03d}.lean")
        ] = support_chunk_text(index, chunk).encode()
    for index, chunk in enumerate(clause_chunks):
        outputs[
            Path(f"ErdosSzekeres/PredecessorHalfFin13ClauseChunk{index:03d}.lean")
        ] = clause_chunk_text(index, chunk).encode()
    for index, (start, stop) in enumerate(semantic_ranges):
        outputs[
            Path(f"ErdosSzekeres/PredecessorHalfFin13SemanticSegment{index:03d}.lean")
        ] = semantic_segment_text(
            index, tuple(entries[start:stop]), start, stop
        ).encode()
    summary = {
        "schema_version": 1,
        "core_cnf_sha256": EXPECTED[CORE_REL / "core.cnf"],
        "core_lrat_sha256": EXPECTED[CORE_REL / "core.lrat"],
        "core_variables": len(core["used_variables"]),
        "core_clauses": len(entries),
        "support_facts": len(facts),
        "support_chunks": len(support_chunks),
        "clause_chunks": len(clause_chunks),
        "semantic_segments": len(semantic_ranges),
    }
    outputs[CORE_REL / "lean-generation-summary.json"] = (
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    ).encode()
    return outputs


def generate(repo: Path, output_root: Path) -> dict[str, str]:
    outputs = generated_outputs(repo)
    for relative, data in outputs.items():
        path = output_root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return {
        str(relative): digest(data)
        for relative, data in sorted(outputs.items(), key=lambda item: str(item[0]))
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--output-root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    hashes = generate(args.repo.resolve(), args.output_root.resolve())
    print(json.dumps(hashes, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
