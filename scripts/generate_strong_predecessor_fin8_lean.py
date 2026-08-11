#!/usr/bin/env python3
"""Generate the kernel-certificate bridge for balanced Fin-8 Property B."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import struct
from dataclasses import dataclass
from pathlib import Path


N = 8
PREFIX = "StrongPredecessorFin8"
CNF_SHA = "75cab86f23e12fb30832c4db875a03b9dcda53f560353423233d31a8a311db0a"
TREE_SHA = "84836242d68a3d9e3a16a1e3ad8c347ead43a33cb6054f42f1a6d386da5cd37c"
TRIPLES = tuple(itertools.combinations(range(N), 3))
QUADS = tuple(itertools.combinations(range(N), 4))
TRIPLE_VAR = {t: i + 1 for i, t in enumerate(TRIPLES)}
QUAD_VAR = {q: len(TRIPLES) + i + 1 for i, q in enumerate(QUADS)}


@dataclass(frozen=True)
class Origin:
    kind: str
    vertices: tuple[int, ...]
    values: tuple[bool, ...] = ()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_if_changed(path: Path, content: str | bytes) -> None:
    payload = content.encode() if isinstance(content, str) else content
    if path.exists() and path.read_bytes() == payload:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(payload)
    os.replace(temporary, path)


def parse_cnf(path: Path):
    variables = clauses_expected = None
    clauses = []
    for line in path.read_text(encoding="ascii").splitlines():
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            _, kind, variables, clauses_expected = line.split()
            if kind != "cnf":
                raise ValueError("not CNF")
            variables, clauses_expected = int(variables), int(clauses_expected)
        else:
            fields = tuple(map(int, line.split()))
            if fields[-1] != 0:
                raise ValueError("unterminated clause")
            clauses.append(fields[:-1])
    if variables != 126 or clauses_expected != len(clauses) or len(clauses) != 1211:
        raise ValueError("unexpected CNF dimensions")
    return variables, tuple(clauses)


def origins():
    result = []
    for q in QUADS:
        result.extend(Origin("signotope", q, tuple(values))
                      for values in itertools.product((False, True), repeat=4)
                      if sum(x != y for x, y in zip(values, values[1:])) > 1)
        result.extend(Origin("strong_def", q) for _ in range(8))
    result.extend(Origin("no_five", f) for f in itertools.combinations(range(N), 5))
    result.extend(Origin("balanced", (0,) + tail)
                  for tail in itertools.combinations(range(1, N), 3))
    return tuple(result)


def propagate_with_hints(clauses, initial):
    assignment = dict(initial)
    hints = []
    while True:
        progress = False
        for clause_id, clause in enumerate(clauses, 1):
            unknown = []
            satisfied = False
            for literal in clause:
                variable = abs(literal)
                if variable not in assignment:
                    unknown.append(literal)
                elif assignment[variable] == (literal > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not unknown:
                hints.append(clause_id)
                return hints
            if len(unknown) == 1:
                literal = unknown[0]
                assignment[abs(literal)] = literal > 0
                hints.append(clause_id)
                progress = True
                break
        if not progress:
            raise ValueError("certificate leaf is not RUP")


def tree_to_lrat(tree_path: Path, clauses):
    data = tree_path.read_bytes()
    if data[:8] != b"PB8TREE1":
        raise ValueError("bad tree magic")
    variables, count, tokens_count = struct.unpack("<III", data[8:20])
    if variables != 126 or count != len(clauses) or len(data) != 20 + 2 * tokens_count:
        raise ValueError("bad tree dimensions")
    tokens = struct.unpack(f"<{tokens_count}h", data[20:])
    next_id = len(clauses) + 1
    lines = []

    def visit(index, path):
        nonlocal next_id
        token = tokens[index]
        index += 1
        candidate = tuple(-v if value else v for v, value in path)
        if token == 0:
            clause_id = next_id
            next_id += 1
            hints = propagate_with_hints(clauses, dict(path))
            lines.append(f"{clause_id} {' '.join(map(str, candidate))} 0 {' '.join(map(str, hints))} 0")
            return index, clause_id
        variable = abs(token)
        first = token < 0
        index, left_id = visit(index, path + ((variable, first),))
        index, right_id = visit(index, path + ((variable, not first),))
        clause_id = next_id
        next_id += 1
        lines.append(f"{clause_id} {' '.join(map(str, candidate))} 0 {left_id} {right_id} 0")
        return index, clause_id

    end, root_id = visit(0, ())
    final_fields = lines[-1].split()
    if end != len(tokens) or final_fields[0] != str(root_id) or final_fields[1] != "0":
        raise ValueError("incomplete tree")
    return ("\n".join(lines) + "\n").encode(), len(lines), root_id


def triple_prop(variable: int) -> str:
    i, j, k = TRIPLES[variable - 1]
    return f"(χ ⟨{i}, {j}, {k}, by decide, by decide⟩ = Turn.left)"


def quad_prop(variable: int) -> str:
    a, b, c, d = QUADS[variable - len(TRIPLES) - 1]
    return f"(StrongPredecessorFin8Quad χ {a} {b} {c} {d} (by decide) (by decide) (by decide))"


def variable_prop(variable: int) -> str:
    return triple_prop(variable) if variable <= len(TRIPLES) else quad_prop(variable)


def atom_name(variable: int) -> str:
    return f"StrongPredecessorFin8Atom{variable:03}"


def atom_prop(variable: int) -> str:
    return f"({atom_name(variable)} χ)"


def balanced_join(items, operator):
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return f"({balanced_join(items[:middle], operator)} {operator} {balanced_join(items[middle:], operator)})"


def rcases_or_pattern(items):
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return f"({rcases_or_pattern(items[:middle])} | {rcases_or_pattern(items[middle:])})"


def chunks(items, count=16):
    if count == 1:
        return [items]
    middle = len(items) // 2
    return chunks(items[:middle], count // 2) + chunks(items[middle:], count // 2)


def not_or(items):
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return f"(fun h ↦ Or.elim h {not_or(items[:middle])} {not_or(items[middle:])})"


def contradiction(proof, clause):
    names = ", ".join(f"h{i}" for i in range(len(clause)))
    cases = " | ".join("hs" for _ in clause)
    atoms = " ".join(atom_name(abs(lit)) for lit in clause)
    goals = "\n".join(
        f"      · exact {'h' + str(i) + ' hs' if lit > 0 else 'hs h' + str(i)}"
        for i, lit in enumerate(clause))
    return f"(by\n      intro hbad\n      have hsat := {proof}\n      unfold {atoms} at hbad\n      rcases hbad with ⟨{names}⟩\n      rcases hsat with {cases}\n{goals})"


def set_literal(vertices):
    return "{" + ", ".join(map(str, vertices)) + "}"


def clause_disjunction(clause):
    literals = [(variable_prop(abs(lit)) if lit > 0 else f"¬{variable_prop(abs(lit))}")
                for lit in clause]
    return balanced_join(literals, "∨")


def semantic_proof(origin, clause):
    if origin.kind == "signotope":
        a, b, c, d = origin.vertices
        targets = ["Turn.left" if value else "Turn.right" for value in origin.values]
        named = " ".join(f"({name} := {target})" for name, target in zip("ABCD", targets))
        return f"(by\n      have hm := turnSequence_mismatch\n        (hsignotope (i := {a}) (j := {b}) (k := {c}) (l := {d}) (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp))\n        {named} (by simp [TurnSequenceAllowed])\n      simpa only [Turn.ne_right_iff_eq_left] using hm)"
    if origin.kind == "strong_def":
        a, b, c, d = origin.vertices
        return f"(by\n      show {clause_disjunction(clause)}\n      have h := strongPredecessorFin8Quad_iff_left χ {a} {b} {c} {d} (by decide) (by decide) (by decide)\n      tauto)"
    if origin.kind == "no_five":
        a, b, c, d, e = origin.vertices
        return f"(by\n      have hnot : ¬ IsStrongPolygonSet χ {set_literal(origin.vertices)} := by\n        intro h\n        exact hnoStrong ⟨{set_literal(origin.vertices)}, by simp, by decide, h⟩\n      exact strongPredecessorFin8_notStrongFive_quads χ {a} {b} {c} {d} {e} (by decide) (by decide) (by decide) (by decide) hnot)"
    red = origin.vertices
    blue = tuple(v for v in range(N) if v not in red)
    a, b, c, d = red
    e, f, g, h = blue
    return f"""(by
      show {clause_disjunction(clause)}
      by_contra hn
      push Not at hn
      have hr : ¬ ContainsStrongPolygonSet χ ({set_literal(red)} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ {a} {b} {c} {d}
          (by decide) (by decide) (by decide)).2 hn.1
      have hb : ¬ ContainsStrongPolygonSet χ ({set_literal(blue)} : Finset (Fin 8)) 4 :=
        (strongPredecessorFin8_notContainsFour_iff χ {e} {f} {g} {h}
          (by decide) (by decide) (by decide)).2 hn.2
      apply hnoBicolor
      refine ⟨{set_literal(red)}, {set_literal(blue)}, ?_, ?_, ?_, ?_, hr, hb⟩
      · decide
      · decide
      · decide
      · decide)"""


def write_base(repo: Path):
    source = '''module

public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace ErdosSzekeres

def StrongPredecessorFin8Quad (χ : TripleColoring 8) (a b c d : Fin 8)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    χ ⟨a, c, d, hab.trans hbc, hcd⟩ = χ ⟨b, c, d, hbc, hcd⟩

theorem strongPredecessorFin8Quad_iff_strongSet (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrongPredecessorFin8Quad χ a b c d hab hbc hcd ↔
      IsStrongPolygonSet χ {a, b, c, d} := by
  constructor
  · rintro ⟨h₁, h₂⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl <;> try omega
    exact ⟨h₁, h₂⟩
  · intro h
    exact h hab hbc hcd (by simp) (by simp) (by simp) (by simp)

theorem strongPredecessorFin8Quad_iff_left (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrongPredecessorFin8Quad χ a b c d hab hbc hcd ↔
      (((χ ⟨a, b, c, hab, hbc⟩ = Turn.left) ↔
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.left)) ∧
       ((χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.left) ↔
        (χ ⟨b, c, d, hbc, hcd⟩ = Turn.left))) := by
  unfold StrongPredecessorFin8Quad
  generalize h₀ : χ ⟨a, b, c, hab, hbc⟩ = x₀
  generalize h₁ : χ ⟨a, b, d, hab, hbc.trans hcd⟩ = x₁
  generalize h₂ : χ ⟨a, c, d, hab.trans hbc, hcd⟩ = x₂
  generalize h₃ : χ ⟨b, c, d, hbc, hcd⟩ = x₃
  cases x₀ <;> cases x₁ <;> cases x₂ <;> cases x₃ <;> simp

theorem strongPredecessorFin8_notStrongFive_quads (χ : TripleColoring 8)
    (a b c d e : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hnot : ¬ IsStrongPolygonSet χ {a, b, c, d, e}) :
    ¬ StrongPredecessorFin8Quad χ a b c d hab hbc hcd ∨
    ¬ StrongPredecessorFin8Quad χ a b c e hab hbc (hcd.trans hde) ∨
    ¬ StrongPredecessorFin8Quad χ a b d e hab (hbc.trans hcd) hde ∨
    ¬ StrongPredecessorFin8Quad χ a c d e (hab.trans hbc) hcd hde ∨
    ¬ StrongPredecessorFin8Quad χ b c d e hbc hcd hde := by
  by_contra h
  push Not at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [StrongPredecessorFin8Quad]

theorem strongPredecessorFin8_containsFour_iff (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ContainsStrongPolygonSet χ {a, b, c, d} 4 ↔
      StrongPredecessorFin8Quad χ a b c d hab hbc hcd := by
  rw [strongPredecessorFin8Quad_iff_strongSet]
  constructor
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    have heq : polygon = {a, b, c, d} := by
      apply Finset.eq_of_subset_of_card_le hsub
      simp [hcard, hab.ne, (hab.trans hbc).ne, (hab.trans (hbc.trans hcd)).ne,
        hbc.ne, (hbc.trans hcd).ne, hcd.ne]
    simpa [heq] using hstrong
  · intro h
    exact ⟨{a, b, c, d}, by simp, by simp [hab.ne, (hab.trans hbc).ne,
      (hab.trans (hbc.trans hcd)).ne, hbc.ne, (hbc.trans hcd).ne, hcd.ne], h⟩

theorem strongPredecessorFin8_notContainsFour_iff (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ¬ ContainsStrongPolygonSet χ {a, b, c, d} 4 ↔
      ¬ StrongPredecessorFin8Quad χ a b c d hab hbc hcd :=
  not_congr (strongPredecessorFin8_containsFour_iff χ a b c d hab hbc hcd)

end ErdosSzekeres

end
'''
    atoms = "\n\n".join(
        f"def {atom_name(variable)} (χ : TripleColoring 8) : Prop :=\n  {variable_prop(variable)}"
        for variable in range(1, 127)
    )
    source = source.replace(
        "\nend ErdosSzekeres\n\nend\n",
        f"\n\n/-- Opaque names keep LRAT atom substitution linear in the certificate bridge. -/\n"
        f"{atoms}\n\nend ErdosSzekeres\n\nend\n",
    )
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Encoding.lean", source)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--source", type=Path, default=Path("runs/agents/20260810-wave1/property-b"))
    parser.add_argument("--audit-output", type=Path,
                        default=Path("runs/agents/20260810-wave2/property-b-lean/generation.json"))
    args = parser.parse_args()
    repo = args.repo.resolve()
    source = args.source if args.source.is_absolute() else repo / args.source
    cnf_source = source / "fin8-balanced-counterexample.cnf"
    tree_source = source / "fin8-balanced-counterexample.tree"
    if sha256(cnf_source) != CNF_SHA or sha256(tree_source) != TREE_SHA:
        raise ValueError("frozen input hash mismatch")
    _, clauses = parse_cnf(cnf_source)
    origin_list = origins()
    if len(origin_list) != len(clauses):
        raise ValueError("origin mismatch")
    lrat, additions, root_id = tree_to_lrat(tree_source, clauses)
    cert_dir = repo / "certificates"
    target_cnf = cert_dir / "strong-predecessor-fin8-balanced.cnf"
    target_lrat = cert_dir / "strong-predecessor-fin8-balanced.lrat"
    write_if_changed(target_cnf, cnf_source.read_bytes())
    write_if_changed(target_lrat, lrat)
    write_base(repo)
    unsat = '''module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

namespace ErdosSzekeres

lrat_proof strongPredecessorFin8_lrat_unsat
  (include_str "../certificates/strong-predecessor-fin8-balanced.cnf")
  (include_str "../certificates/strong-predecessor-fin8-balanced.lrat")

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Unsat.lean", unsat)
    bad_props = []
    proofs = []
    for clause, origin in zip(clauses, origin_list):
        literals = [(f"¬{atom_prop(abs(lit))}" if lit > 0 else atom_prop(abs(lit)))
                    for lit in clause]
        bad_props.append("(" + " ∧ ".join(literals) + ")")
        proofs.append(contradiction(semantic_proof(origin, clause), clause))
    prop_chunks = chunks(bad_props)
    proof_chunks = chunks(proofs)
    header = '''@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace ErdosSzekeres

'''
    for index, (props, items) in enumerate(zip(prop_chunks, proof_chunks)):
        name = f"{PREFIX}BadChunk{index}"
        content = f"module\n\npublic import ErdosSzekeres.{PREFIX}Encoding\n\n{header}"
        content += f"def {name} (χ : TripleColoring 8) : Prop :=\n  {balanced_join(props, '∨')}\n\n"
        content += f"theorem strongPredecessorFin8_chunk{index}_of_constraints (χ : TripleColoring 8) (hsignotope : OneChangeOn χ Finset.univ) (hnoStrong : ¬ ContainsStrongPolygonSet χ Finset.univ 5) (hnoBicolor : ¬ ∃ red blue : Finset (Fin 8), Disjoint red blue ∧ red ∪ blue = Finset.univ ∧ red.card = 4 ∧ blue.card = 4 ∧ ¬ ContainsStrongPolygonSet χ red 4 ∧ ¬ ContainsStrongPolygonSet χ blue 4) : ¬ {name} χ := by\n  unfold {name}\n  exact {not_or(items)}\n\nend ErdosSzekeres\n\nend\n"
        write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}CNFChunk{index:02}.lean", content)
    imports = "\n".join(f"public import ErdosSzekeres.{PREFIX}CNFChunk{i:02}" for i in range(16))
    imports += f"\npublic import ErdosSzekeres.{PREFIX}Unsat"
    chunk_names = [f"{PREFIX}BadChunk{i}" for i in range(16)]
    args_props = " ".join(atom_prop(i) for i in range(1, 127))
    haves = "\n  ".join(f"have h{i} := strongPredecessorFin8_chunk{i}_of_constraints χ hsignotope hnoStrong hnoBicolor" for i in range(16))
    cases = rcases_or_pattern([f"hbad{i}" for i in range(16)])
    closes = "\n".join(
        f"  · apply h{index}\n    unfold {chunk_names[index]}\n    exact hbad{index}"
        for index in range(16)
    )
    root = f'''module

{imports}

{header}theorem strongPredecessorFin8_constraints_false (χ : TripleColoring 8)
    (hsignotope : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ ContainsStrongPolygonSet χ Finset.univ 5)
    (hnoBicolor : ¬ ∃ red blue : Finset (Fin 8), Disjoint red blue ∧
      red ∪ blue = Finset.univ ∧ red.card = 4 ∧ blue.card = 4 ∧
      ¬ ContainsStrongPolygonSet χ red 4 ∧ ¬ ContainsStrongPolygonSet χ blue 4) :
    False := by
  {haves}
  have hcertificate := strongPredecessorFin8_lrat_unsat {args_props}
  rcases hcertificate with {cases}
{closes}

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}CNFGenerated.lean", root)
    final = f'''module

public import ErdosSzekeres.{PREFIX}CNFGenerated

@[expose] public section

namespace ErdosSzekeres

theorem strongFiveFreeSignotopeFinEight_balancedBicoloring
    (χ : TripleColoring 8) (hsignotope : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ ContainsStrongPolygonSet χ Finset.univ 5) :
    ∃ red blue : Finset (Fin 8), Disjoint red blue ∧
      red ∪ blue = Finset.univ ∧ red.card = 4 ∧ blue.card = 4 ∧
      ¬ ContainsStrongPolygonSet χ red 4 ∧
      ¬ ContainsStrongPolygonSet χ blue 4 := by
  by_contra hnoBicolor
  exact strongPredecessorFin8_constraints_false χ hsignotope hnoStrong hnoBicolor

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Certificate.lean", final)
    audit = {"schema_version": 1, "cnf_sha256": sha256(target_cnf),
             "lrat_sha256": sha256(target_lrat), "lrat_bytes": len(lrat),
             "lrat_additions": additions, "root_id": root_id}
    audit_path = args.audit_output if args.audit_output.is_absolute() else repo / args.audit_output
    write_if_changed(audit_path, json.dumps(audit, indent=2, sort_keys=True) + "\n")
    print(json.dumps(audit, sort_keys=True))


if __name__ == "__main__":
    main()
