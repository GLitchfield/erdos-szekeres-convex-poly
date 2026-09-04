#!/usr/bin/env python3
"""Generate the Lean semantic reflection of the anchored Fin15 LRAT core.

Modeled on ``generate_predecessor_half_fin13_lean.py``.  The SAT encoding
has three kinds of atoms (triple colors, strong quadruples, strong five-sets)
plus the anchor units.  Inputs frozen under
``certificates/fin15-anchored-checkpoints/``: ``core.cnf`` (dependency core
with densely renumbered variables), ``core-base-ids.txt`` (one-based indices
into the stream of ``generate_fin15_anchored_sat.py``), and
``core-variable-map.txt`` (old variable, new variable).  The checkpoint
modules ``Fin15AnchoredCheckpoint*`` come from ``split_lrat_checkpoints.py
--compact-final``.

The generated final theorem: every anchored one-change coloring on fifteen
vertices without a strong six-set has an eight-point support without a
strong five-set.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from generate_fin15_anchored_sat import (
    FIVE_BY_VAR, QUAD_BY_VAR, TRIPLE_BY_VAR, annotated_formula, quad_triples,
)

CERT_REL = Path("certificates/fin15-anchored-checkpoints")
PREFIX = "Fin15Anchored"
SUPPORT_CHUNK_SIZE = 40
CLAUSE_CHUNK_SIZE = 128
SEMANTIC_SEGMENT_DEPTH = 7


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_cnf(text: str):
    clauses = []
    variables = None
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        fields = line.split()
        if fields[0] == "p":
            variables = int(fields[2])
            continue
        values = tuple(map(int, fields))
        clauses.append(values[:-1])
    return variables, clauses


def load_core(repo: Path):
    entries_all, _ = annotated_formula()
    variables, core_clauses = parse_cnf((repo / CERT_REL / "core.cnf").read_text())
    ids = [int(x) for x in (repo / CERT_REL / "core-base-ids.txt").read_text().split()]
    variable_map = {}
    for line in (repo / CERT_REL / "core-variable-map.txt").read_text().splitlines():
        old, new = map(int, line.split())
        variable_map[old] = new
    used_old = sorted(variable_map)
    if [variable_map[old] for old in used_old] != list(range(1, len(used_old) + 1)):
        raise ValueError("core variable map is not dense")
    if variables != len(used_old):
        raise ValueError("core variable count differs from the map")
    entries = []
    for position, clause_id in enumerate(ids):
        entry = dict(entries_all[clause_id - 1])
        renumbered = tuple(
            (variable_map[abs(l)] if l > 0 else -variable_map[abs(l)])
            for l in entry["literals"])
        if renumbered != core_clauses[position]:
            raise ValueError(f"core clause {position} differs from original {clause_id}")
        entry["core_literals"] = renumbered
        entry["index"] = position
        entries.append(entry)
    return {"entries": entries, "used_variables": used_old, "variable_map": variable_map}


# ------------------------------------------------------------- naming

def finset(vertices) -> str:
    return "{" + ", ".join(map(str, vertices)) + "}"


def mask(vertices) -> int:
    return sum(1 << v for v in vertices)


def atom_name(old_variable: int) -> str:
    return f"{PREFIX}Atom{old_variable:04d}"


def atom_term(old_variable: int) -> str:
    return f"{atom_name(old_variable)} chi"


def triple_term(triple) -> str:
    a, b, c = triple
    return f"chi ⟨{a}, {b}, {c}, by decide, by decide⟩"


def strong_quad_term(quad) -> str:
    a, b, c, d = quad
    return f"{PREFIX}StrongQuad chi {a} {b} {c} {d} (by decide) (by decide) (by decide)"


def header(imports) -> list[str]:
    lines = ["module", ""]
    lines += [f"public import {name}" for name in imports]
    lines += [
        "",
        "@[expose] public section",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 30000",
        "set_option linter.unusedSimpArgs false",
        "set_option linter.unusedVariables false",
        "",
        "namespace ErdosSzekeres",
        "",
    ]
    return lines


def footer() -> list[str]:
    return ["end ErdosSzekeres", "", "end", ""]


# ---------------------------------------------------------- encoding

def encoding_text(core) -> str:
    lines = header(["ErdosSzekeres.AnchoredPresentation",
                    "ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport"])
    lines += [
        "/-- The exact Fin15 support conclusion certified by the LRAT core. -/",
        f"def {PREFIX}Conclusion (chi : TripleColoring 15) : Prop :=",
        "  ∃ support : Finset (Fin 15),",
        "    support.card = 8 ∧",
        "    ¬ContainsStrongPolygonSet chi support 5",
        "",
        "/-- The two equalities contributed by one ordered quadruple to the",
        "strong-polygon predicate. -/",
        f"def {PREFIX}StrongQuad (chi : TripleColoring 15)",
        "    (a b c d : Fin 15) (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=",
        "  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧",
        "    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩",
        "",
    ]
    for variable in core["used_variables"]:
        lines.append(f"def {atom_name(variable)} (chi : TripleColoring 15) : Prop :=")
        if variable in TRIPLE_BY_VAR:
            lines.append(f"  {triple_term(TRIPLE_BY_VAR[variable])} = Turn.left")
        elif variable in QUAD_BY_VAR:
            lines.append(f"  {strong_quad_term(QUAD_BY_VAR[variable])}")
        elif variable in FIVE_BY_VAR:
            lines.append(f"  IsStrongPolygonSet chi {finset(FIVE_BY_VAR[variable])}")
        else:
            raise ValueError(variable)
        lines.append("")
    lines += footer()
    return "\n".join(lines)


# ----------------------------------------------------- support facts

def strong_set_iff_lines(five) -> list[str]:
    quads = tuple(itertools.combinations(five, 4))
    name = f"fin15Anchored_strongSet_iff_mask{mask(five):05d}"
    lines = [f"theorem {name} (chi : TripleColoring 15) :",
             f"    IsStrongPolygonSet chi {finset(five)} ↔"]
    for index, quad in enumerate(quads):
        suffix = " ∧" if index + 1 < len(quads) else " := by"
        lines.append(f"      {strong_quad_term(quad)}{suffix}")
    lines += ["  constructor", "  · intro h",
              "    refine ⟨" + ", ".join("?_" for _ in quads) + "⟩"]
    for a, b, c, d in quads:
        lines += [
            f"    · simpa [{PREFIX}StrongQuad] using h",
            f"        (i := {a}) (j := {b}) (k := {c}) (l := {d})",
            "        (by decide) (by decide) (by decide)",
            "        (by simp) (by simp) (by simp) (by simp)",
        ]
    facts = ", ".join(f"h{i}" for i in range(len(quads)))
    choices = " | ".join("rfl" for _ in five)
    lines += [
        f"  · rintro ⟨{facts}⟩ i j k l hij hjk hkl hi hj hk hl",
        "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl",
        f"    rcases hi with {choices} <;>",
        f"      rcases hj with {choices} <;>",
        f"      rcases hk with {choices} <;>",
        f"      rcases hl with {choices} <;> try omega",
        f"    all_goals simp_all [{PREFIX}StrongQuad]",
    ]
    return lines


def sublists_len_aux(n, items, wrap, acc):
    """Mirror of Lean's ``List.sublistsLenAux`` so that emitted families are in
    exactly the order ``(E.powersetCard 5).val`` evaluates to."""
    if n == 0:
        return [wrap([])] + acc
    if not items:
        return acc
    head, rest = items[0], items[1:]
    inner = sublists_len_aux(n - 1, rest, lambda xs, head=head, wrap=wrap: wrap([head] + xs), acc)
    return sublists_len_aux(n, rest, wrap, inner)


def sublists_len(n, items):
    return sublists_len_aux(n, list(items), lambda xs: xs, [])


def five_subset_lines(eight) -> list[str]:
    """Every five-subset of ``eight`` is one of its 56 five-subsets.

    The enumeration is a definitional computation: ``(E.powersetCard 5).val``
    reduces by ``rfl`` to the literal list of five-sets in ``sublistsLen``
    order, and membership in that list is the required disjunction.  This
    replaces a 512-way case split that took hours per file."""
    fives = [tuple(five) for five in sublists_len(5, eight)]
    name = f"fin15Anchored_fiveSubset_mask{mask(eight):05d}"
    family = f"fin15Anchored_fiveFamily_mask{mask(eight):05d}"
    listing = ", ".join(finset(five) for five in fives)
    lines = [f"theorem {family} :",
             f"    (({finset(eight)} : Finset (Fin 15)).powersetCard 5).val =",
             f"      (↑([{listing}] : List (Finset (Fin 15))) :",
             "        Multiset (Finset (Fin 15))) := rfl",
             "",
             f"theorem {name} :",
             f"    ∀ polygon : Finset (Fin 15), polygon ⊆ {finset(eight)} →",
             "      polygon.card = 5 →"]
    for index, five in enumerate(fives):
        suffix = " ∨" if index + 1 < len(fives) else " := by"
        lines.append(f"        polygon = {finset(five)}{suffix}")
    lines += [
        "  intro polygon hsubset hcard",
        f"  have hmem : polygon ∈ (({finset(eight)} : Finset (Fin 15)).powersetCard 5).val :=",
        "    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)",
        f"  rw [{family}] at hmem",
        "  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem",
        "  exact hmem",
    ]
    return lines


def support_facts(core):
    strong_fives = {tuple(e["origin"]["five"]) for e in core["entries"]
                    if e["category"] == "strong_five_definition"}
    for e in core["entries"]:
        if e["category"] == "no_strong_six":
            for five in itertools.combinations(tuple(e["origin"]["six"]), 5):
                strong_fives.add(five)
    eights = {tuple(e["origin"]["eight"]) for e in core["entries"]
              if e["category"] == "every_eight_has_strong_five"}
    facts = [("five", v) for v in sorted(strong_fives)]
    facts += [("eight", v) for v in sorted(eights)]
    return tuple(facts)


def support_chunk_text(index, facts) -> str:
    lines = header([f"ErdosSzekeres.{PREFIX}Encoding"])
    lines += [f"/-! Semantic helper facts in bounded group {index:03d}. -/", ""]
    for kind, vertices in facts:
        lines += strong_set_iff_lines(vertices) if kind == "five" else five_subset_lines(vertices)
        lines.append("")
    lines += footer()
    return "\n".join(lines)


def support_text(chunk_count) -> str:
    imports = [f"ErdosSzekeres.{PREFIX}SupportSegment{i:03d}" for i in range(chunk_count)]
    return "\n".join(header(imports) + footer())


# ---------------------------------------------------------- clauses

def failure_expression(literals) -> str:
    return " ∧\n      ".join(
        f"¬{atom_term(abs(l))}" if l > 0 else atom_term(abs(l)) for l in literals)


def unfold_lines(literals) -> list[str]:
    names = [atom_name(v) for v in sorted({abs(l) for l in literals})]
    rows = ["  unfold " + names[0]]
    for name in names[1:]:
        if len(rows[-1]) + len(name) + 1 < 96:
            rows[-1] += " " + name
        else:
            rows.append("    " + name)
    rows[-1] += " at hbad"
    return rows


def color_cases(quad, *, one_change: bool) -> list[str]:
    lines = []
    for index, triple in enumerate(quad_triples(quad)):
        lines.append("  " + "  " * index + f"cases hcolor{index} : {triple_term(triple)} <;>")
    simp = "TurnSequenceAllowed, " if one_change else ""
    lines.append(f"          simp_all [{simp}{PREFIX}StrongQuad]")
    return lines


def clause_lemma(entry) -> list[str]:
    index = entry["index"]
    category = entry["category"]
    origin = entry["origin"]
    literals = entry["literals"]  # original numbering: atom names use old variables
    lines = [f"theorem fin15Anchored_clause{index:05d} (chi : TripleColoring 15)"]
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
        lines += [f"    : ¬({failure_expression(literals)}) := by", "  intro hbad"]
        lines += unfold_lines(literals)
        lines += color_cases(tuple(origin["quad"]), one_change=False)
    elif category == "strong_five_definition":
        five = tuple(origin["five"])
        lines += [f"    : ¬({failure_expression(literals)}) := by", "  intro hbad"]
        lines += unfold_lines(literals)
        lines += ["  simp only [", f"    fin15Anchored_strongSet_iff_mask{mask(five):05d}",
                  "  ] at hbad", "  tauto"]
    elif category == "no_strong_six":
        six = tuple(origin["six"])
        # hbad is the conjunction of the six five-atoms in literal order; the
        # statement of the enumeration is in sublistsLen order.
        literal_fives = [tuple(FIVE_BY_VAR[abs(l)]) for l in literals]
        family_fives = [tuple(five) for five in sublists_len(5, six)]
        names = [f"n{i}" for i in range(len(literal_fives))]
        listing = ", ".join(finset(five) for five in family_fives)
        lines += [
            "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :",
            f"    ¬({failure_expression(literals)}) := by",
            "  intro hbad",
        ]
        lines += unfold_lines(literals)
        lines += [
            f"  obtain ⟨{', '.join(names)}⟩ := hbad",
            "  apply hnoStrong",
            f"  refine ⟨{finset(six)}, by simp, by decide, ?_⟩",
            "  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_",
            "  intro t hsub hcard",
            f"  have hmem : t ∈ (({finset(six)} : Finset (Fin 15)).powersetCard 5).val :=",
            "    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)",
            f"  have hfam : (({finset(six)} : Finset (Fin 15)).powersetCard 5).val =",
            f"      (↑([{listing}] : List (Finset (Fin 15))) :",
            "        Multiset (Finset (Fin 15))) := rfl",
            "  rw [hfam] at hmem",
            "  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem",
            "  rcases hmem with " + " | ".join("rfl" for _ in family_fives),
        ]
        for five in family_fives:
            lines.append(f"  · exact n{literal_fives.index(five)}")
    elif category == "every_eight_has_strong_five":
        eight = tuple(origin["eight"])
        # Order of the disjunction produced by ``five_subset_lines`` (sublistsLen
        # order) versus the order of the clause's literals (the conjuncts of hbad).
        statement_fives = [tuple(five) for five in sublists_len(5, eight)]
        literal_fives = [tuple(FIVE_BY_VAR[abs(l)]) for l in literals]
        names = [f"n{i}" for i in range(len(literal_fives))]
        lines += [
            f"    (hno : ¬{PREFIX}Conclusion chi) :",
            f"    ¬({failure_expression(literals)}) := by",
            "  intro hbad",
            "  apply hno",
            f"  refine ⟨{finset(eight)}, by decide, ?_⟩",
            "  rintro ⟨polygon, hsubset, hcard, hstrong⟩",
            f"  have heq := fin15Anchored_fiveSubset_mask{mask(eight):05d}",
            "    polygon hsubset hcard",
        ]
        lines += unfold_lines(literals)
        lines.append(f"  obtain ⟨{', '.join(names)}⟩ := hbad")
        lines.append("  rcases heq with " + " | ".join("rfl" for _ in statement_fives))
        for five in statement_fives:
            lines.append(f"  · exact absurd hstrong n{literal_fives.index(five)}")
    elif category == "anchor":
        _, i, j = origin["triple"]
        lines += [
            "    (hanchor : chi.IsAnchored) :",
            f"    ¬({failure_expression(literals)}) := by",
            "  intro hbad",
        ]
        lines += unfold_lines(literals)
        lines += [
            f"  have hr := hanchor (i := {i}) (j := {j}) (by decide) (by decide)",
            "  rw [hbad] at hr",
            "  cases hr",
        ]
    else:
        raise ValueError(category)
    return lines


def clause_chunk_text(index, entries) -> str:
    imports = [f"ErdosSzekeres.{PREFIX}Support"]
    if any(entry["category"] == "no_strong_six" for entry in entries):
        imports.append("ErdosSzekeres.StrongPolygonSubsets")
    lines = header(imports)
    lines += [f"/-! Retained anchored Fin15 semantic clauses in bounded group {index:03d}. -/", ""]
    for entry in entries:
        lines += clause_lemma(entry)
        lines.append("")
    lines += footer()
    return "\n".join(lines)


def clause_application(entry) -> str:
    lemma = f"fin15Anchored_clause{entry['index']:05d} chi"
    extra = {"one_change": " hone", "no_strong_six": " hnoStrong",
             "every_eight_has_strong_five": " hno", "anchor": " hanchor"}
    return lemma + extra.get(entry["category"], "")


def balanced_ranges(start, stop, depth):
    if depth == 0:
        return ((start, stop),)
    middle = start + (stop - start) // 2
    return balanced_ranges(start, middle, depth - 1) + balanced_ranges(middle, stop, depth - 1)


def balanced_failure_expression(entries) -> str:
    if len(entries) == 1:
        return f"({failure_expression(entries[0]['literals'])})"
    middle = len(entries) // 2
    return (f"({balanced_failure_expression(entries[:middle])} ∨\n      "
            f"{balanced_failure_expression(entries[middle:])})")


def reject_tree_lines(entries, indent) -> list[str]:
    if len(entries) == 1:
        return [f"{indent}exact {clause_application(entries[0])} hbad"]
    middle = len(entries) // 2
    lines = [f"{indent}rcases hbad with hbad | hbad", f"{indent}·"]
    lines += reject_tree_lines(entries[:middle], indent + "  ")
    lines.append(f"{indent}·")
    lines += reject_tree_lines(entries[middle:], indent + "  ")
    return lines


HYPOTHESES = [
    "    (chi : TripleColoring 15)",
    "    (hone : OneChangeOn chi Finset.univ)",
    "    (hanchor : chi.IsAnchored)",
    "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)",
    f"    (hno : ¬{PREFIX}Conclusion chi)",
]


def semantic_segment_text(index, entries, start, stop) -> str:
    first_chunk = start // CLAUSE_CHUNK_SIZE
    last_chunk = (stop - 1) // CLAUSE_CHUNK_SIZE
    imports = [f"ErdosSzekeres.{PREFIX}ClauseChunk{c:03d}" for c in range(first_chunk, last_chunk + 1)]
    lines = header(imports)
    lines += [f"/-! Semantic rejection of balanced CNF subtree {index:03d}. -/", "",
              f"theorem fin15Anchored_rejectSemanticSegment{index:03d}"]
    lines += HYPOTHESES[:-1] + [HYPOTHESES[-1] + " :"]
    lines += [f"    ¬({balanced_failure_expression(entries)}) := by", "  intro hbad"]
    lines += reject_tree_lines(entries, "  ")
    lines.append("")
    lines += footer()
    return "\n".join(lines)


def reject_segment_tree_lines(segments, indent) -> list[str]:
    if len(segments) == 1:
        return [f"{indent}exact fin15Anchored_rejectSemanticSegment{segments[0]:03d}",
                f"{indent}  chi hone hanchor hnoStrong hno hbad"]
    middle = len(segments) // 2
    lines = [f"{indent}rcases hbad with hbad | hbad", f"{indent}·"]
    lines += reject_segment_tree_lines(segments[:middle], indent + "  ")
    lines.append(f"{indent}·")
    lines += reject_segment_tree_lines(segments[middle:], indent + "  ")
    return lines


def unsat_alias_text(segment_count) -> str:
    return "\n".join([
        "module", "",
        f"public import ErdosSzekeres.{PREFIX}CheckpointSegment{segment_count - 1:03d}",
        "", "@[expose] public section", "", "namespace ErdosSzekeres", "",
        "/-! Public alias for the checkpointed, kernel-checked anchored Fin15 refutation. -/",
        "run_cmd",
        "  Lean.Elab.Command.liftTermElabM do",
        f"    let sourceName := `ErdosSzekeres.{PREFIX}Checkpoint.publicUnsat",
        "    let targetName := `ErdosSzekeres.fin15Anchored_lrat_unsat",
        "    let info ← Lean.getConstInfo sourceName",
        "    Lean.withExporting do",
        "      Lean.addDecl <| .thmDecl {",
        "        name := targetName",
        "        levelParams := info.levelParams",
        "        type := info.type",
        "        value := Lean.mkConst sourceName (info.levelParams.map Lean.mkLevelParam)",
        "      }",
        "", "end ErdosSzekeres", "", "end", ""])


def final_text(core, segment_count) -> str:
    imports = [f"ErdosSzekeres.{PREFIX}Unsat", "ErdosSzekeres.AnchoredFin15Consumer"]
    imports += [f"ErdosSzekeres.{PREFIX}SemanticSegment{i:03d}" for i in range(segment_count)]
    lines = header(imports)
    lines += [
        "/-- Every anchored one-change coloring on fifteen vertices without a strong",
        "six-set has an eight-point support without a strong five-set. -/",
        "theorem fin15AnchoredConclusion_of_oneChange",
        "    (chi : TripleColoring 15)",
        "    (hone : OneChangeOn chi Finset.univ)",
        "    (hanchor : chi.IsAnchored)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :",
        f"    {PREFIX}Conclusion chi := by",
        "  by_contra hno",
        "  have hbad := fin15Anchored_lrat_unsat",
    ]
    atoms = [f"({atom_term(v)})" for v in core["used_variables"]]
    for start in range(0, len(atoms), 4):
        lines.append("    " + " ".join(atoms[start:start + 4]))
    lines += [f"  unfold {PREFIX}Checkpoint.bad at hbad"]
    lines += reject_segment_tree_lines(list(range(segment_count)), "  ")
    lines += [
        "",
        "/-- The anchored Fin15 endpoint in the form consumed by the middle producer. -/",
        "theorem fin15Anchored_endpoint (chi : TripleColoring 15)",
        "    (hone : OneChangeOn chi Finset.univ) (hanchor : chi.IsAnchored)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :",
        "    ∃ support : Finset (Fin 15),",
        "      support.card = 8 ∧ ¬ContainsStrongPolygonSet chi support 5 :=",
        "  fin15AnchoredConclusion_of_oneChange chi hone hanchor hnoStrong",
        "",
        "/-- Ambient cardinalities fifteen and sixteen of the fixed-six predecessor-half",
        "theorem, unconditionally. -/",
        "theorem predecessorHalfSubsetAtSixMiddle : PredecessorHalfSubsetAtSixMiddle :=",
        "  predecessorHalfSubsetAtSixMiddle_of_anchoredFin15Endpoint fin15Anchored_endpoint",
        "",
    ]
    lines += footer()
    return "\n".join(lines)


def generated_outputs(repo: Path, segment_count: int):
    core = load_core(repo)
    facts = support_facts(core)
    support_chunks = [tuple(facts[s:s + SUPPORT_CHUNK_SIZE]) for s in range(0, len(facts), SUPPORT_CHUNK_SIZE)]
    entries = core["entries"]
    clause_chunks = [tuple(entries[s:s + CLAUSE_CHUNK_SIZE]) for s in range(0, len(entries), CLAUSE_CHUNK_SIZE)]
    semantic_ranges = balanced_ranges(0, len(entries), SEMANTIC_SEGMENT_DEPTH)
    outputs = {
        Path(f"ErdosSzekeres/{PREFIX}Encoding.lean"): encoding_text(core).encode(),
        Path(f"ErdosSzekeres/{PREFIX}Support.lean"): support_text(len(support_chunks)).encode(),
        Path(f"ErdosSzekeres/{PREFIX}Unsat.lean"): unsat_alias_text(segment_count).encode(),
        Path(f"ErdosSzekeres/{PREFIX}.lean"): final_text(core, len(semantic_ranges)).encode(),
    }
    for i, chunk in enumerate(support_chunks):
        outputs[Path(f"ErdosSzekeres/{PREFIX}SupportSegment{i:03d}.lean")] = support_chunk_text(i, chunk).encode()
    for i, chunk in enumerate(clause_chunks):
        outputs[Path(f"ErdosSzekeres/{PREFIX}ClauseChunk{i:03d}.lean")] = clause_chunk_text(i, chunk).encode()
    for i, (start, stop) in enumerate(semantic_ranges):
        outputs[Path(f"ErdosSzekeres/{PREFIX}SemanticSegment{i:03d}.lean")] = \
            semantic_segment_text(i, entries[start:stop], start, stop).encode()
    summary = {
        "schema_version": 1,
        "core_cnf_sha256": digest((repo / CERT_REL / "core.cnf").read_bytes()),
        "core_variables": len(core["used_variables"]),
        "core_clauses": len(entries),
        "support_facts": len(facts),
        "support_chunks": len(support_chunks),
        "clause_chunks": len(clause_chunks),
        "semantic_segments": len(semantic_ranges),
        "checkpoint_segments": segment_count,
        "categories": {c: sum(1 for e in entries if e["category"] == c) for c in
                       ("one_change", "strong_quad_definition", "strong_five_definition",
                        "no_strong_six", "every_eight_has_strong_five", "anchor")},
    }
    outputs[CERT_REL / "lean-generation-summary.json"] = (json.dumps(summary, indent=2, sort_keys=True) + "\n").encode()
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--segments", type=int, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    outputs = generated_outputs(repo, args.segments)
    for relative, data in outputs.items():
        path = repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    summary = json.loads(outputs[CERT_REL / "lean-generation-summary.json"])
    print(json.dumps(summary, indent=2, sort_keys=True))
    print(f"wrote {len(outputs)} files")


if __name__ == "__main__":
    main()
