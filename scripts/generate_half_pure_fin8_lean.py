#!/usr/bin/env python3
"""Generate the exact Fin8 half-pure LRAT and Lean semantic bridge."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


SOURCE_REL = Path("runs/agents/20260811-post-checkpoint-wave/half-pure-fin8-certificate")
EXPECTED = {
    "formula.cnf": "95120d1910cf0ec469445a1575024ca5997769b41ea51a3e6e9f750f2ca89f2a",
    "clause-map.json": "dcebe1055585e7a1e3882803adade57f0fa17fbd0785c38f7f6c821e9f0fac84",
    "proof-core.lrat": "780e549d2b1223e39a617ddf1e101491a0ab00e79d8e046124eba8c373a71200",
    "core-summary.json": "4bee16e7c372b95bb8b17115841e0fb67ca729c728002b3a44a66557aa35cf7e",
}
TRIPLES = tuple(itertools.combinations(range(8), 3))
QUADS = tuple(itertools.combinations(range(8), 4))
TVAR = {triple: index + 1 for index, triple in enumerate(TRIPLES)}
SVAR = {quad: 57 + index for index, quad in enumerate(QUADS)}
LBAD = {quad: 127 + index for index, quad in enumerate(QUADS)}
UBAD = {quad: 197 + index for index, quad in enumerate(QUADS)}
CLAUSE_CHUNK_SIZE = 24


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_frozen(source: Path, name: str) -> bytes:
    data = (source / name).read_bytes()
    if digest(data) != EXPECTED[name]:
        raise ValueError(f"frozen input hash mismatch: {name}")
    return data


def parse_dimacs(data: bytes):
    variable_count = None
    clauses = []
    for text in data.decode().splitlines():
        if not text or text.startswith("c"):
            continue
        fields = text.split()
        if fields[0] == "p":
            variable_count = int(fields[2])
            expected_clauses = int(fields[3])
            continue
        values = tuple(map(int, fields))
        if not values or values[-1] != 0:
            raise ValueError("unterminated DIMACS clause")
        clauses.append(values[:-1])
    if variable_count is None or len(clauses) != expected_clauses:
        raise ValueError("bad DIMACS header")
    return variable_count, tuple(clauses)


def parse_lrat(data: bytes):
    records = []
    for text in data.decode().splitlines():
        fields = text.split()
        if not fields:
            continue
        if len(fields) > 1 and fields[1] == "d":
            raise ValueError("compact frozen proof unexpectedly contains a deletion")
        old_id = int(fields[0])
        separator = fields.index("0", 1)
        clause = tuple(map(int, fields[1:separator]))
        hints = tuple(map(int, fields[separator + 1:-1]))
        if fields[-1] != "0":
            raise ValueError("unterminated LRAT hints")
        records.append((old_id, clause, hints))
    return tuple(records)


def dense_core(formula: bytes, proof: bytes, summary_data: bytes):
    variable_count, clauses = parse_dimacs(formula)
    summary = json.loads(summary_data)
    base_ids = tuple(summary["initial_core_clause_ids"])
    records = parse_lrat(proof)
    if variable_count != 266 or len(base_ids) != 483 or len(records) != 261:
        raise ValueError("unexpected frozen core dimensions")
    mapping = {old: new for new, old in enumerate(base_ids, 1)}
    next_id = len(base_ids) + 1
    for old_id, _clause, _hints in records:
        mapping[old_id] = next_id
        next_id += 1
    core_clauses = tuple(clauses[old - 1] for old in base_ids)
    cnf_rows = [f"p cnf {variable_count} {len(core_clauses)}"]
    cnf_rows.extend(" ".join(map(str, clause)) + " 0" for clause in core_clauses)
    lrat_rows = []
    for old_id, clause, hints in records:
        if any(hint not in mapping for hint in hints):
            raise ValueError(f"unmapped LRAT hint in clause {old_id}")
        row = [str(mapping[old_id]), *(str(x) for x in clause), "0",
               *(str(mapping[x]) for x in hints), "0"]
        lrat_rows.append(" ".join(row))
    return (("\n".join(cnf_rows) + "\n").encode(),
            ("\n".join(lrat_rows) + "\n").encode(), base_ids)


def atom_name(variable: int) -> str:
    return f"HalfPureDeepSplitFin8Atom{variable:03d}"


def atom_term(variable: int) -> str:
    return f"{atom_name(variable)} χ"


def finset(vertices) -> str:
    return "{" + ", ".join(map(str, vertices)) + "}"


def triple_term(triple) -> str:
    a, b, c = triple
    return f"χ ⟨{a}, {b}, {c}, by decide, by decide⟩"


def quad_keys(quad):
    a, b, c, d = quad
    return ((a, b, c), (a, b, d), (a, c, d), (b, c, d))


def lean_header(import_name: str) -> list[str]:
    return [
        "module",
        "",
        f"public import {import_name}",
        "",
        "@[expose] public section",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 20000",
        "set_option linter.unusedSimpArgs false",
        "",
        "namespace ErdosSzekeres",
        "",
    ]


def encoding_text(core_entries) -> str:
    lines = lean_header("ErdosSzekeres.StrongPredecessorFin8Encoding")
    lines += [
        "/-- The exact bounded conclusion certified by the Fin8 LRAT proof. -/",
        "def HalfPureDeepSplitFin8Conclusion (χ : TripleColoring 8) : Prop :=",
        "  ∃ lower upper : Finset (Fin 8),",
        "    HasDeepBelowSplit χ lower upper ∧",
        "    ((upper.Nonempty ∧ 8 ≤ 2 * lower.card ∧",
        "        ∀ polygon : Finset (Fin 8),",
        "          polygon ⊆ lower → polygon.card = 5 - 1 →",
        "            IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨",
        "     (lower.Nonempty ∧ 8 ≤ 2 * upper.card ∧",
        "        ∀ polygon : Finset (Fin 8),",
        "          polygon ⊆ upper → polygon.card = 5 - 1 →",
        "            IsStrongPolygonSet χ polygon → IsCapSet χ polygon))",
        "",
        "theorem halfPureDeepSplitFin8_isCupSet_four_iff (χ : TripleColoring 8)",
        "    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :",
        "    IsCupSet χ {a, b, c, d} ↔",
        "      χ ⟨a, b, c, hab, hbc⟩ = Turn.left ∧",
        "      χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.left ∧",
        "      χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.left ∧",
        "      χ ⟨b, c, d, hbc, hcd⟩ = Turn.left := by",
        "  constructor",
        "  · intro h",
        "    exact ⟨h _ (by simp) (by simp) (by simp),",
        "      h _ (by simp) (by simp) (by simp),",
        "      h _ (by simp) (by simp) (by simp),",
        "      h _ (by simp) (by simp) (by simp)⟩",
        "  · rintro ⟨h₀, h₁, h₂, h₃⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk",
        "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk",
        "    rcases hi with rfl | rfl | rfl | rfl <;>",
        "      rcases hj with rfl | rfl | rfl | rfl <;>",
        "      rcases hk with rfl | rfl | rfl | rfl <;> try omega",
        "",
        "theorem halfPureDeepSplitFin8_isCapSet_four_iff (χ : TripleColoring 8)",
        "    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :",
        "    IsCapSet χ {a, b, c, d} ↔",
        "      χ ⟨a, b, c, hab, hbc⟩ = Turn.right ∧",
        "      χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.right ∧",
        "      χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.right ∧",
        "      χ ⟨b, c, d, hbc, hcd⟩ = Turn.right := by",
        "  constructor",
        "  · intro h",
        "    exact ⟨h _ (by simp) (by simp) (by simp),",
        "      h _ (by simp) (by simp) (by simp),",
        "      h _ (by simp) (by simp) (by simp),",
        "      h _ (by simp) (by simp) (by simp)⟩",
        "  · rintro ⟨h₀, h₁, h₂, h₃⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk",
        "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk",
        "    rcases hi with rfl | rfl | rfl | rfl <;>",
        "      rcases hj with rfl | rfl | rfl | rfl <;>",
        "      rcases hk with rfl | rfl | rfl | rfl <;> try omega",
        "",
    ]
    for variable, triple in enumerate(TRIPLES, 1):
        lines += [
            f"def {atom_name(variable)} (χ : TripleColoring 8) : Prop :=",
            f"  {triple_term(triple)} = Turn.left",
            "",
        ]
    for quad in QUADS:
        a, b, c, d = quad
        lines += [
            f"def {atom_name(SVAR[quad])} (χ : TripleColoring 8) : Prop :=",
            f"  StrongPredecessorFin8Quad χ {a} {b} {c} {d}",
            "    (by decide) (by decide) (by decide)",
            "",
        ]
    for quad in QUADS:
        a, b, c, d = quad
        lines += [
            f"def {atom_name(LBAD[quad])} (χ : TripleColoring 8) : Prop :=",
            f"  StrongPredecessorFin8Quad χ {a} {b} {c} {d}",
            "      (by decide) (by decide) (by decide) ∧",
            f"    ¬IsCupSet χ {finset(quad)}",
            "",
        ]
    for quad in QUADS:
        a, b, c, d = quad
        lines += [
            f"def {atom_name(UBAD[quad])} (χ : TripleColoring 8) : Prop :=",
            f"  StrongPredecessorFin8Quad χ {a} {b} {c} {d}",
            "      (by decide) (by decide) (by decide) ∧",
            f"    ¬IsCapSet χ {finset(quad)}",
            "",
        ]
    side_masks = set()
    for entry in core_entries:
        if entry["category"] == "lower_no_witness":
            side_masks.add(entry["origin"]["lower_mask"])
        if entry["category"] == "upper_no_witness":
            side_masks.add(entry["origin"]["upper_mask"])
    for mask in sorted(side_masks):
        vertices = tuple(i for i in range(8) if mask >> i & 1)
        if len(vertices) != 4:
            raise ValueError("retained branch side is not a four-set")
        lines += [
            f"theorem halfPureDeepSplitFin8_fourSubset_eq_mask{mask:03d} :",
            f"    ∀ polygon : Finset (Fin 8), polygon ⊆ {finset(vertices)} →",
            f"      polygon.card = 4 → polygon = {finset(vertices)} := by decide",
            "",
        ]
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def failure_expression(literals) -> str:
    pieces = []
    for literal in literals:
        atom = atom_term(abs(literal))
        pieces.append(f"¬{atom}" if literal > 0 else atom)
    return " ∧\n      ".join(pieces)


def unfold_line(literals, suffix="at hbad") -> list[str]:
    names = [atom_name(variable) for variable in sorted({abs(x) for x in literals})]
    result = ["  unfold " + names[0]]
    for name in names[1:]:
        if len(result[-1]) + 1 + len(name) < 96:
            result[-1] += " " + name
        else:
            result.append("    " + name)
    result[-1] += " " + suffix
    return result


def case_colors(quad) -> list[str]:
    keys = quad_keys(tuple(quad))
    lines = []
    for index, key in enumerate(keys):
        indent = "  " + "  " * index
        tail = " <;>" if index < 3 else " <;>"
        lines.append(f"{indent}cases hcolor{index} : {triple_term(key)}{tail}")
    lines.append("          simp_all [TurnSequenceAllowed, StrongPredecessorFin8Quad,")
    lines.append("            halfPureDeepSplitFin8_isCupSet_four_iff,")
    lines.append("            halfPureDeepSplitFin8_isCapSet_four_iff]")
    return lines


def one_change_lemma(entry) -> list[str]:
    clause_id = entry["id"]
    quad = entry["origin"]["quad"]
    a, b, c, d = quad
    lines = [
        f"theorem halfPureDeepSplitFin8_clause{clause_id:04d} (χ : TripleColoring 8)",
        "    (hone : OneChangeOn χ Finset.univ) :",
        f"    ¬({failure_expression(entry['literals'])}) := by",
        "  intro hbad",
        f"  have hallowed := hone (i := {a}) (j := {b}) (k := {c}) (l := {d})",
        "    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)",
    ]
    lines += unfold_line(entry["literals"])
    lines += case_colors(quad)
    return lines


def definition_lemma(entry) -> list[str]:
    clause_id = entry["id"]
    quad = entry["origin"]["quad"]
    lines = [
        f"theorem halfPureDeepSplitFin8_clause{clause_id:04d} (χ : TripleColoring 8) :",
        f"    ¬({failure_expression(entry['literals'])}) := by",
        "  intro hbad",
    ]
    lines += unfold_line(entry["literals"])
    lines += case_colors(quad)
    return lines


def no_strong_lemma(entry) -> list[str]:
    clause_id = entry["id"]
    five = entry["origin"]["five"]
    a, b, c, d, e = five
    lines = [
        f"theorem halfPureDeepSplitFin8_clause{clause_id:04d} (χ : TripleColoring 8)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :",
        f"    ¬({failure_expression(entry['literals'])}) := by",
        "  intro hbad",
        f"  have hnot : ¬IsStrongPolygonSet χ {finset(five)} := by",
        "    intro hstrong",
        f"    exact hnoStrong ⟨{finset(five)}, by simp, by decide, hstrong⟩",
        "  have hor := strongPredecessorFin8_notStrongFive_quads χ",
        f"    {a} {b} {c} {d} {e} (by decide) (by decide) (by decide) (by decide) hnot",
    ]
    lines += unfold_line(entry["literals"])
    lines.append("  tauto")
    return lines


def branch_lemma(entry) -> list[str]:
    clause_id = entry["id"]
    category = entry["category"]
    origin = entry["origin"]
    lower = tuple(origin["lower_vertices"])
    upper = tuple(origin["upper_vertices"])
    union_size = len(set(lower) | set(upper))
    if sorted((len(lower), len(upper))) != [1, 4] or union_size != 5:
        raise ValueError(f"retained clause {clause_id} is not a 4+1 branch")
    if len(entry["literals"]) != 7:
        raise ValueError(f"retained branch clause {clause_id} is not seven-literal")
    side = lower if category == "lower_no_witness" else upper
    bad_variable = abs(entry["literals"][-1])
    expected_bad = LBAD[tuple(side)] if category == "lower_no_witness" else UBAD[tuple(side)]
    if bad_variable != expected_bad or entry["literals"][-1] < 0:
        raise ValueError(f"retained branch clause {clause_id} has wrong bad atom")
    facts = [f"h{index}" for index in range(7)]
    branch = "Or.inl" if category == "lower_no_witness" else "Or.inr"
    pure = "IsCupSet" if category == "lower_no_witness" else "IsCapSet"
    side_mask = origin["lower_mask"] if category == "lower_no_witness" else origin["upper_mask"]
    a, b, c, d = side
    lines = [
        f"theorem halfPureDeepSplitFin8_clause{clause_id:04d} (χ : TripleColoring 8)",
        "    (hno : ¬HalfPureDeepSplitFin8Conclusion χ) :",
        f"    ¬({failure_expression(entry['literals'])}) := by",
        f"  rintro ⟨{', '.join(facts)}⟩",
    ]
    for index, literal in enumerate(entry["literals"]):
        lines.append(f"  unfold {atom_name(abs(literal))} at h{index}")
    lines += [
        "  apply hno",
        "  unfold HalfPureDeepSplitFin8Conclusion",
        f"  refine ⟨{finset(lower)}, {finset(upper)}, ?_, {branch} ?_⟩",
        "  · refine ⟨by decide, ?_⟩",
        "    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper",
        "    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, or_assoc] at hi hj hk",
        "    rcases hi with rfl | rfl | rfl | rfl | rfl <;>",
        "      rcases hj with rfl | rfl | rfl | rfl | rfl <;>",
        "        rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega",
        "    all_goals cases hcolor : χ ⟨_, _, _, _, _⟩ <;> simp_all",
        "  · refine ⟨by simp, by decide, ?_⟩",
        "    intro polygon hsub hcard hstrong",
        f"    have heq := halfPureDeepSplitFin8_fourSubset_eq_mask{side_mask:03d}",
        "      polygon hsub (by omega)",
        "    subst polygon",
        f"    show {pure} χ {finset(side)}",
        "    by_contra hnotPure",
        "    apply h6",
        "    exact ⟨(strongPredecessorFin8Quad_iff_strongSet χ",
        f"      {a} {b} {c} {d} (by decide) (by decide) (by decide)).mpr hstrong, hnotPure⟩",
    ]
    return lines


def clause_lemma(entry) -> list[str]:
    category = entry["category"]
    if category == "one_change":
        return one_change_lemma(entry)
    if category in {"strong_quad_definition", "lower_bad_definition",
                    "upper_bad_definition"}:
        return definition_lemma(entry)
    if category == "no_strong_five":
        return no_strong_lemma(entry)
    if category in {"lower_no_witness", "upper_no_witness"}:
        return branch_lemma(entry)
    raise ValueError(f"unknown category {category}")


def clause_chunk_text(index: int, entries) -> str:
    lines = lean_header("ErdosSzekeres.HalfPureDeepSplitFin8Encoding")
    lines.append(f"/-! Semantic clauses for retained LRAT leaf chunk {index}. -/")
    lines.append("")
    for entry in entries:
        lines += clause_lemma(entry)
        lines.append("")
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def unsat_text() -> str:
    return """module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

namespace ErdosSzekeres

lrat_proof halfPureDeepSplitFin8_lrat_unsat
  (include_str "../certificates/half-pure-deep-split-fin8-core.cnf")
  (include_str "../certificates/half-pure-deep-split-fin8-core.lrat")

end ErdosSzekeres

end
"""


def final_text(core_entries, chunk_count: int) -> str:
    lines = ["module", "", "public import ErdosSzekeres.HalfPureDeepSplitFin8Unsat"]
    lines += [f"public import ErdosSzekeres.HalfPureDeepSplitFin8ClauseChunk{i:02d}"
              for i in range(chunk_count)]
    lines += [
        "public import ErdosSzekeres.InverseSteppingUpKernel",
        "",
        "@[expose] public section",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 20000",
        "set_option linter.unusedSimpArgs false",
        "",
        "namespace ErdosSzekeres",
        "",
        "/-- Normalized exact Fin8 conclusion certified by the compact LRAT proof. -/",
        "theorem halfPureDeepSplitFin8Conclusion_of_oneChange",
        "    (χ : TripleColoring 8)",
        "    (hone : OneChangeOn χ Finset.univ)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :",
        "    HalfPureDeepSplitFin8Conclusion χ := by",
        "  by_contra hno",
        "  have hbad := halfPureDeepSplitFin8_lrat_unsat",
    ]
    atoms = [f"({atom_term(i)})" for i in range(1, 267)]
    for start in range(0, len(atoms), 6):
        lines.append("    " + " ".join(atoms[start:start + 6]))
    lines.append("  simp only [")
    for index, entry in enumerate(core_entries):
        category = entry["category"]
        lemma = f"halfPureDeepSplitFin8_clause{entry['id']:04d} χ"
        if category == "one_change":
            lemma += " hone"
        elif category == "no_strong_five":
            lemma += " hnoStrong"
        elif category in {"lower_no_witness", "upper_no_witness"}:
            lemma += " hno"
        lines.append(f"    {lemma},")
    lines.append("    false_or, or_false")
    lines += [
        "  ] at hbad",
        "",
        "/-- Exact Fin8 half-pure deep-split theorem under the rank-three one-change law. -/",
        "theorem halfPureDeepSplitAtFiveFinEight_of_oneChange",
        "    (χ : TripleColoring 8)",
        "    (hone : OneChangeOn χ Finset.univ)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 5) :",
        "    ∃ lower upper : Finset (Fin 8),",
        "      HasDeepBelowSplit χ lower upper ∧",
        "      ((upper.Nonempty ∧ 8 ≤ 2 * lower.card ∧",
        "          ∀ polygon : Finset (Fin 8),",
        "            polygon ⊆ lower → polygon.card = 5 - 1 →",
        "              IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨",
        "       (lower.Nonempty ∧ 8 ≤ 2 * upper.card ∧",
        "          ∀ polygon : Finset (Fin 8),",
        "            polygon ⊆ upper → polygon.card = 5 - 1 →",
        "              IsStrongPolygonSet χ polygon → IsCapSet χ polygon)) := by",
        "  simpa only [HalfPureDeepSplitFin8Conclusion] using",
        "    halfPureDeepSplitFin8Conclusion_of_oneChange χ hone hnoStrong",
        "",
        "end ErdosSzekeres",
        "",
        "end",
        "",
    ]
    return "\n".join(lines)


def generated_outputs(repo: Path):
    source = repo / SOURCE_REL
    formula = read_frozen(source, "formula.cnf")
    clause_map_data = read_frozen(source, "clause-map.json")
    proof = read_frozen(source, "proof-core.lrat")
    summary_data = read_frozen(source, "core-summary.json")
    core_cnf, core_lrat, base_ids = dense_core(formula, proof, summary_data)
    clause_map = json.loads(clause_map_data)
    core_entries = [clause_map["clauses"][clause_id - 1] for clause_id in base_ids]
    chunks = [core_entries[start:start + CLAUSE_CHUNK_SIZE]
              for start in range(0, len(core_entries), CLAUSE_CHUNK_SIZE)]
    outputs = {
        Path("certificates/half-pure-deep-split-fin8.cnf"): formula,
        Path("certificates/half-pure-deep-split-fin8.lrat"): proof,
        Path("certificates/half-pure-deep-split-fin8-core.cnf"): core_cnf,
        Path("certificates/half-pure-deep-split-fin8-core.lrat"): core_lrat,
        Path("ErdosSzekeres/HalfPureDeepSplitFin8Encoding.lean"):
            encoding_text(core_entries).encode(),
        Path("ErdosSzekeres/HalfPureDeepSplitFin8Unsat.lean"): unsat_text().encode(),
        Path("ErdosSzekeres/HalfPureDeepSplitFin8.lean"):
            final_text(core_entries, len(chunks)).encode(),
    }
    for index, chunk in enumerate(chunks):
        outputs[Path(f"ErdosSzekeres/HalfPureDeepSplitFin8ClauseChunk{index:02d}.lean")] = (
            clause_chunk_text(index, chunk).encode())
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
    manifest = generate(args.repo.resolve(), args.output_root.resolve())
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
