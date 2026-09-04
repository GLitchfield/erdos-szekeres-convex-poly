#!/usr/bin/env python3
"""Generate the Lean semantic reflection of the anchored ES(6) LRAT core.

Inputs (frozen under ``certificates/es6-anchored-checkpoints/``):

* ``core.cnf``: the dependency core of the anchored 17-point instance, whose
  clauses are the original clauses listed in ``core-base-ids.txt`` (one-based
  indices into the stream produced by ``generate_es6_anchored_sat.py``), in
  that order, over the unchanged 680 triple variables;
* the checkpoint modules ``ES6AnchoredCheckpointContext`` and
  ``ES6AnchoredCheckpointSegmentNNN`` written by
  ``split_lrat_checkpoints.py --compact-final``, whose final segment exports
  ``ES6AnchoredCheckpoint.publicUnsat : ∀ atoms, ES6AnchoredCheckpoint.bad atoms``.

Outputs:

* ``ES6AnchoredClauseChunkNNN.lean``: one lemma per core clause deriving it
  from the one-change law, the absence of strong six-sets, or the anchor;
* ``ES6AnchoredSemanticSegmentNNN.lean``: rejection of one balanced subtree
  of the reified formula;
* ``ES6AnchoredUnsat.lean``: public alias of the kernel-checked refutation;
* ``ES6Anchored.lean``: the theorem that every anchored one-change coloring
  on seventeen vertices contains a strong six-set.

The balanced tree shapes mirror ``Mathlib.Tactic.Sat.buildConj`` exactly
(``mid = start + (stop - start) / 2``), as in the Fin13 generator.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from generate_es6_anchored_sat import N, TRIPLE_BY_VAR, generate

CERT_REL = Path("certificates/es6-anchored-checkpoints")
CLAUSE_CHUNK_SIZE = 128
SEMANTIC_SEGMENT_DEPTH = 7
PREFIX = "ES6Anchored"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_cnf(text: str) -> tuple[int, list[tuple[int, ...]]]:
    variables = None
    clauses = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        fields = line.split()
        if fields[0] == "p":
            variables = int(fields[2])
            continue
        values = tuple(map(int, fields))
        if values[-1] != 0:
            raise ValueError("unterminated clause")
        clauses.append(values[:-1])
    return variables, clauses


def load_core(repo: Path):
    records = generate()
    core_text = (repo / CERT_REL / "core.cnf").read_text()
    variables, core_clauses = parse_cnf(core_text)
    if variables != 680:
        raise ValueError("unexpected variable count in core")
    ids = [int(x) for x in (repo / CERT_REL / "core-base-ids.txt").read_text().split()]
    if len(ids) != len(core_clauses):
        raise ValueError("core id list and core clause count differ")
    entries = []
    for position, clause_id in enumerate(ids):
        category, owner, values, literals = records[clause_id - 1]
        if tuple(literals) != core_clauses[position]:
            raise ValueError(f"core clause {position} differs from original {clause_id}")
        entries.append({
            "index": position,
            "id": clause_id,
            "category": category,
            "owner": owner,
            "values": values,
            "literals": tuple(literals),
        })
    return entries


# ----------------------------------------------------------------- Lean text

def header(imports: list[str]) -> list[str]:
    lines = ["module", ""]
    lines += [f"public import {name}" for name in imports]
    lines += [
        "",
        "@[expose] public section",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 30000",
        "set_option linter.unusedVariables false",
        "set_option linter.unusedSimpArgs false",
        "",
        "namespace ErdosSzekeres",
        "",
    ]
    return lines


def footer() -> list[str]:
    return ["end ErdosSzekeres", "", "end", ""]


def triple_term(variable: int) -> str:
    a, b, c = TRIPLE_BY_VAR[variable]
    return f"(chi ⟨{a}, {b}, {c}, by decide, by decide⟩ = Turn.left)"


def failure_expression(literals: tuple[int, ...]) -> str:
    return " ∧\n      ".join(
        f"¬{triple_term(abs(literal))}" if literal > 0 else triple_term(abs(literal))
        for literal in literals
    )


ASSUMPTIONS = """    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored)"""


def clause_lemma(entry) -> list[str]:
    name = f"es6Anchored_clause{entry['index']:05d}"
    literals = entry["literals"]
    category = entry["category"]
    lines = [f"theorem {name} (chi : TripleColoring 17)", ASSUMPTIONS + " :",
             f"    ¬({failure_expression(literals)}) := by", "  intro hbad"]
    targets = ["Turn.left" if value else "Turn.right" for value in entry["values"]]
    if category == "one_change":
        a, b, c, d = entry["owner"]
        named = " ".join(f"({n} := {t})" for n, t in zip("ABCD", targets))
        lines += [
            f"  have hm := turnSequence_mismatch",
            f"    (hallowed {a} {b} {c} {d} (by decide) (by decide) (by decide))",
            f"    {named} (by simp [TurnSequenceAllowed])",
            "  simp only [Turn.ne_right_iff_eq_left] at hm",
        ]
    elif category == "no_strong_six":
        vector = ", ".join(map(str, entry["owner"]))
        named = " ".join(f"(x{i} := {t})" for i, t in enumerate(targets))
        lines += [
            f"  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![{vector}] (by decide)",
            f"  have hm := strongSix_mismatch chi f (hno f) {named}",
            "    (by simp [StrongSixValues])",
            "  simp only [f, Turn.ne_right_iff_eq_left] at hm",
        ]
    elif category == "anchor":
        _, i, j = entry["owner"]
        lines += [
            f"  have hr := hanchor (i := {i}) (j := {j}) (by decide) (by decide)",
            "  rw [hbad] at hr",
            "  cases hr",
        ]
        return lines
    else:
        raise ValueError(category)
    # hm : disjunction of the clause's literal semantics; hbad : conjunction of
    # their negations, in the same order.
    count = len(literals)
    bad_names = ", ".join(f"hb{i}" for i in range(count))
    cases = " | ".join(f"hs" for _ in range(count))
    lines.append(f"  rcases hbad with ⟨{bad_names}⟩")
    lines.append(f"  rcases hm with {cases}")
    for i, literal in enumerate(literals):
        if literal > 0:
            lines.append(f"  · exact hb{i} hs")
        else:
            lines.append(f"  · exact hs hb{i}")
    return lines


def clause_chunk_text(index: int, entries) -> str:
    lines = header([f"ErdosSzekeres.{PREFIX}Encoding"])
    lines += [f"/-! Retained anchored ES(6) semantic clauses, group {index:03d}. -/", ""]
    for entry in entries:
        lines += clause_lemma(entry)
        lines.append("")
    lines += footer()
    return "\n".join(lines)


def balanced_ranges(start: int, stop: int, depth: int):
    if depth == 0:
        return ((start, stop),)
    middle = start + (stop - start) // 2
    return balanced_ranges(start, middle, depth - 1) + balanced_ranges(middle, stop, depth - 1)


def balanced_failure_expression(entries) -> str:
    if len(entries) == 1:
        return f"({failure_expression(entries[0]['literals'])})"
    middle = len(entries) // 2
    left = balanced_failure_expression(entries[:middle])
    right = balanced_failure_expression(entries[middle:])
    return f"({left} ∨\n      {right})"


def reject_tree_lines(entries, indent: str) -> list[str]:
    if len(entries) == 1:
        return [f"{indent}exact es6Anchored_clause{entries[0]['index']:05d} chi hallowed hno hanchor hbad"]
    middle = len(entries) // 2
    lines = [f"{indent}rcases hbad with hbad | hbad", f"{indent}·"]
    lines += reject_tree_lines(entries[:middle], indent + "  ")
    lines.append(f"{indent}·")
    lines += reject_tree_lines(entries[middle:], indent + "  ")
    return lines


def semantic_segment_text(index: int, entries, start: int, stop: int) -> str:
    first_chunk = start // CLAUSE_CHUNK_SIZE
    last_chunk = (stop - 1) // CLAUSE_CHUNK_SIZE
    imports = [f"ErdosSzekeres.{PREFIX}ClauseChunk{chunk:03d}"
               for chunk in range(first_chunk, last_chunk + 1)]
    lines = header(imports)
    lines += [
        f"/-! Semantic rejection of balanced CNF subtree {index:03d}. -/",
        "",
        f"theorem es6Anchored_rejectSemanticSegment{index:03d}",
        "    (chi : TripleColoring 17)",
        ASSUMPTIONS + " :",
        f"    ¬({balanced_failure_expression(entries)}) := by",
        "  intro hbad",
    ]
    lines += reject_tree_lines(entries, "  ")
    lines.append("")
    lines += footer()
    return "\n".join(lines)


def reject_segment_tree_lines(segments, indent: str) -> list[str]:
    if len(segments) == 1:
        index = segments[0]
        return [f"{indent}exact es6Anchored_rejectSemanticSegment{index:03d}",
                f"{indent}  chi hallowed hno hanchor hbad"]
    middle = len(segments) // 2
    lines = [f"{indent}rcases hbad with hbad | hbad", f"{indent}·"]
    lines += reject_segment_tree_lines(segments[:middle], indent + "  ")
    lines.append(f"{indent}·")
    lines += reject_segment_tree_lines(segments[middle:], indent + "  ")
    return lines


def unsat_alias_text(segment_count: int) -> str:
    lines = ["module", "",
             f"public import ErdosSzekeres.{PREFIX}CheckpointSegment{segment_count - 1:03d}",
             "", "@[expose] public section", "", "namespace ErdosSzekeres", "",
             "/-! Public alias for the checkpointed, kernel-checked anchored ES(6) refutation. -/",
             "run_cmd",
             "  Lean.Elab.Command.liftTermElabM do",
             f"    let sourceName := `ErdosSzekeres.{PREFIX}Checkpoint.publicUnsat",
             f"    let targetName := `ErdosSzekeres.es6Anchored_lrat_unsat",
             "    let info ← Lean.getConstInfo sourceName",
             "    Lean.withExporting do",
             "      Lean.addDecl <| .thmDecl {",
             "        name := targetName",
             "        levelParams := info.levelParams",
             "        type := info.type",
             "        value := Lean.mkConst sourceName (info.levelParams.map Lean.mkLevelParam)",
             "      }",
             "", "end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def final_text(segment_count: int) -> str:
    imports = [f"ErdosSzekeres.{PREFIX}Unsat"]
    imports += [f"ErdosSzekeres.{PREFIX}SemanticSegment{index:03d}"
                for index in range(segment_count)]
    lines = header(imports)
    lines += [
        "/-- Every anchored one-change coloring on seventeen vertices contains a",
        "strong six-set: the kernel-checked LRAT refutation of the anchored",
        "signotope instance, read back through the semantic clause lemmas. -/",
        "theorem es6Anchored_of_oneChange (chi : TripleColoring 17)",
        "    (hone : OneChangeOn chi Finset.univ) (hanchor : chi.IsAnchored) :",
        "    ContainsStrongPolygonSet chi Finset.univ 6 := by",
        "  by_contra hnoStrong",
        "  have hallowed : ∀ (a b c d : Fin 17),",
        "      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),",
        "      TurnSequenceAllowed",
        "        (chi ⟨a, b, c, hab, hbc⟩)",
        "        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)",
        "        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)",
        "        (chi ⟨b, c, d, hbc, hcd⟩) :=",
        "    fun a b c d hab hbc hcd =>",
        "      hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)",
        "  have hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f :=",
        "    fun f hf => hnoStrong (containsStrongPolygonSet_univ_of_isStrongPolygonOn hf)",
        "  have hbad := es6Anchored_lrat_unsat",
    ]
    atoms = [f"{triple_term(variable)}" for variable in range(1, 681)]
    for start in range(0, len(atoms), 3):
        lines.append("    " + " ".join(atoms[start:start + 3]))
    lines += [f"  unfold {PREFIX}Checkpoint.bad at hbad"]
    lines += reject_segment_tree_lines(list(range(segment_count)), "  ")
    lines.append("")
    lines += footer()
    return "\n".join(lines)


def encoding_text() -> str:
    """Fixed lemmas: the strong-six values, the mismatch lemma, and the
    consumer bridge from an increasing six-embedding to the set predicate."""
    local = list(itertools.combinations(range(6), 3))
    position = {t: i for i, t in enumerate(local)}
    quads = list(itertools.combinations(range(6), 4))
    conditions = []
    for i, j, k, l in quads:
        conditions.append((position[(i, j, k)], position[(i, j, l)]))
        conditions.append((position[(i, k, l)], position[(j, k, l)]))
    values = " ".join(f"x{i}" for i in range(20))
    cond_text = " ∧\n  ".join(f"x{a} = x{b}" for a, b in conditions)
    triple_args = "\n".join(
        f"        (χ ⟨f {a}, f {b}, f {c}, f.strictMono (by decide), f.strictMono (by decide)⟩)"
        for a, b, c in local)
    lines = header(["ErdosSzekeres.ES5Encoding", "ErdosSzekeres.AnchoredPresentation"])
    lines += [
        "/-- The fifteen four-tuple consistency conditions on the twenty triples of",
        "six ordered vertices, in lexicographic triple order. -/",
        f"def StrongSixValues ({values} : Turn) : Prop :=",
        "  " + cond_text,
        "",
        "theorem isStrongPolygonOn_finSix_iff {n : ℕ} (χ : TripleColoring n)",
        "    (f : Fin 6 ↪o Fin n) :",
        "    IsStrongPolygonOn χ f ↔",
        "      StrongSixValues",
        triple_args + " := by",
        "  constructor",
        "  · intro h",
    ]
    names = []
    for i, j, k, l in quads:
        name = f"h{i}{j}{k}{l}"
        names.append(name)
        lines.append(f"    have {name} := h (i := {i}) (j := {j}) (k := {k}) (l := {l})")
        lines.append("      (by decide) (by decide) (by decide)")
    parts = []
    for name in names:
        parts.append(f"{name}.1")
        parts.append(f"{name}.2")
    lines.append("    exact ⟨" + ", ".join(parts) + "⟩")
    hyp_names = []
    for name in names:
        hyp_names.append(name + "a")
        hyp_names.append(name + "b")
    lines.append("  · rintro ⟨" + ", ".join(hyp_names) + "⟩ i j k l hij hjk hkl")
    # nested case analysis on i < j < k < l in Fin 6
    def branch(indent, fixed):
        depth = len(fixed)
        var = "ijkl"[depth]
        low = (fixed[-1] + 1) if fixed else 0
        high = 5 - (3 - depth)
        options = list(range(low, high + 1))
        out = []
        if len(options) == 1:
            value = options[0]
            out.append(f"{indent}have h{var} : {var} = {value} := by omega")
            out.append(f"{indent}subst h{var}")
            new_fixed = fixed + [value]
            if depth == 3:
                i, j, k, l = new_fixed
                out.append(f"{indent}exact ⟨h{i}{j}{k}{l}a, h{i}{j}{k}{l}b⟩")
            else:
                out += branch(indent, new_fixed)
        else:
            alts = " ∨ ".join(f"{var} = {value}" for value in options)
            out.append(f"{indent}have h{var} : {alts} := by omega")
            pattern = " | ".join("rfl" for _ in options)
            out.append(f"{indent}rcases h{var} with {pattern}")
            for value in options:
                new_fixed = fixed + [value]
                if depth == 3:
                    i, j, k, l = new_fixed
                    out.append(f"{indent}· exact ⟨h{i}{j}{k}{l}a, h{i}{j}{k}{l}b⟩")
                else:
                    sub = branch(indent + "  ", new_fixed)
                    out.append(f"{indent}· " + sub[0].strip())
                    out += sub[1:]
        return out
    lines += branch("    ", [])
    lines += [
        "",
        "/-- If a selected six-set is not strong, it differs from every strong target",
        "assignment on at least one of its twenty triple colors. -/",
        "theorem strongSix_mismatch {n : ℕ} (χ : TripleColoring n)",
        "    (f : Fin 6 ↪o Fin n) (hnot : ¬ IsStrongPolygonOn χ f)",
        f"    {{{values} : Turn}}",
        f"    (htarget : StrongSixValues {values}) :",
    ]
    disj = []
    for index, (a, b, c) in enumerate(local):
        disj.append(f"    χ ⟨f {a}, f {b}, f {c}, f.strictMono (by decide), f.strictMono (by decide)⟩ ≠ x{index}")
    lines.append(" ∨\n".join(disj) + " := by")
    lines += [
        "  by_contra h",
        "  push Not at h",
        "  rcases h with ⟨" + ", ".join(f"h{i}" for i in range(20)) + "⟩",
        "  apply hnot",
        "  rw [isStrongPolygonOn_finSix_iff]",
        "  simpa [" + ", ".join(f"h{i}" for i in range(20)) + "] using htarget",
        "",
        "/-- An increasing strong six-embedding witnesses a strong six-set. -/",
        "theorem containsStrongPolygonSet_univ_of_isStrongPolygonOn {n : ℕ}",
        "    {χ : TripleColoring n} {f : Fin 6 ↪o Fin n} (h : IsStrongPolygonOn χ f) :",
        "    ContainsStrongPolygonSet χ Finset.univ 6 :=",
        "  ⟨Finset.univ.image f, Finset.subset_univ _,",
        "    by rw [Finset.card_image_of_injective _ f.injective]; simp,",
        "    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image h⟩",
        "",
    ]
    lines += footer()
    return "\n".join(lines)


def generated_outputs(repo: Path, segment_count: int):
    entries = load_core(repo)
    clause_chunks = [tuple(entries[start:start + CLAUSE_CHUNK_SIZE])
                     for start in range(0, len(entries), CLAUSE_CHUNK_SIZE)]
    semantic_ranges = balanced_ranges(0, len(entries), SEMANTIC_SEGMENT_DEPTH)
    outputs = {
        Path(f"ErdosSzekeres/{PREFIX}Encoding.lean"): encoding_text().encode(),
        Path(f"ErdosSzekeres/{PREFIX}Unsat.lean"): unsat_alias_text(segment_count).encode(),
        Path(f"ErdosSzekeres/{PREFIX}.lean"): final_text(len(semantic_ranges)).encode(),
    }
    for index, chunk in enumerate(clause_chunks):
        outputs[Path(f"ErdosSzekeres/{PREFIX}ClauseChunk{index:03d}.lean")] = \
            clause_chunk_text(index, chunk).encode()
    for index, (start, stop) in enumerate(semantic_ranges):
        outputs[Path(f"ErdosSzekeres/{PREFIX}SemanticSegment{index:03d}.lean")] = \
            semantic_segment_text(index, entries[start:stop], start, stop).encode()
    summary = {
        "schema_version": 1,
        "core_cnf_sha256": digest((repo / CERT_REL / "core.cnf").read_bytes()),
        "core_clauses": len(entries),
        "clause_chunks": len(clause_chunks),
        "semantic_segments": len(semantic_ranges),
        "checkpoint_segments": segment_count,
        "categories": {
            category: sum(1 for e in entries if e["category"] == category)
            for category in ("one_change", "no_strong_six", "anchor")
        },
    }
    outputs[CERT_REL / "lean-generation-summary.json"] = (
        json.dumps(summary, indent=2, sort_keys=True) + "\n").encode()
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--segments", type=int, default=768)
    parser.add_argument("--only-encoding", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()
    if args.only_encoding:
        path = repo / f"ErdosSzekeres/{PREFIX}Encoding.lean"
        path.write_text(encoding_text())
        print(path)
        return
    outputs = generated_outputs(repo, args.segments)
    for relative, data in outputs.items():
        path = repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    print(json.dumps({str(k): digest(v) for k, v in sorted(outputs.items(), key=lambda kv: str(kv[0]))
                      if not str(k).startswith("ErdosSzekeres/ES6AnchoredClauseChunk")
                      and not str(k).startswith("ErdosSzekeres/ES6AnchoredSemanticSegment")},
                     indent=2))
    print(f"wrote {len(outputs)} files")


if __name__ == "__main__":
    main()
