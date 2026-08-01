#!/usr/bin/env python3
"""Generate the rank-three signotope certificate sources for ES(5).

Variables are increasing triples of {0,...,8}; true means a left turn. The
CNF imposes the one-change axiom on every quadruple and forbids every strong
five-vertex coloring on every five-subset. The generated Lean modules connect
those clauses to the project's sweep API and the separately checked LRAT
theorem.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path


def triples(vertices: range | tuple[int, ...]):
    return list(itertools.combinations(vertices, 3))


def is_one_change(bits: tuple[bool, ...]) -> bool:
    return sum(a != b for a, b in zip(bits, bits[1:])) <= 1


def is_strong_five(bit_by_triple: dict[tuple[int, int, int], bool]) -> bool:
    for i, j, k, l in itertools.combinations(range(5), 4):
        if bit_by_triple[i, j, k] != bit_by_triple[i, j, l]:
            return False
        if bit_by_triple[i, k, l] != bit_by_triple[j, k, l]:
            return False
    return True


def forbid_assignment(
    variables: dict[tuple[int, int, int], int],
    keys: list[tuple[int, int, int]],
    bits: tuple[bool, ...],
) -> list[int]:
    return [
        -variables[key] if bit else variables[key]
        for key, bit in zip(keys, bits)
    ]


def balanced_join(items: list[str], operator: str) -> str:
    if len(items) == 1:
        return items[0]
    midpoint = len(items) // 2
    return (
        f"({balanced_join(items[:midpoint], operator)} {operator} "
        f"{balanced_join(items[midpoint:], operator)})"
    )


def balanced_not_or_proof(items: list[str]) -> str:
    if len(items) == 1:
        return items[0]
    midpoint = len(items) // 2
    return (
        "(fun h ↦ Or.elim h "
        + balanced_not_or_proof(items[:midpoint])
        + " "
        + balanced_not_or_proof(items[midpoint:])
        + ")"
    )


def generate() -> tuple[
    list[tuple[int, int, int]],
    list[list[int]],
    list[tuple[str, tuple[int, ...], tuple[bool, ...]]],
]:
    all_triples = triples(range(9))
    variables = {triple: index + 1 for index, triple in enumerate(all_triples)}
    clauses: list[list[int]] = []
    origins: list[tuple[str, tuple[int, ...], tuple[bool, ...]]] = []

    for a, b, c, d in itertools.combinations(range(9), 4):
        keys = [(a, b, c), (a, b, d), (a, c, d), (b, c, d)]
        for bits in itertools.product((False, True), repeat=4):
            if not is_one_change(bits):
                clauses.append(forbid_assignment(variables, keys, bits))
                origins.append(("quad", (a, b, c, d), bits))

    local_triples = triples(range(5))
    strong_patterns = []
    for bits in itertools.product((False, True), repeat=len(local_triples)):
        if is_strong_five(dict(zip(local_triples, bits))):
            strong_patterns.append(bits)

    for subset in itertools.combinations(range(9), 5):
        keys = [tuple(subset[i] for i in triple) for triple in local_triples]
        for bits in strong_patterns:
            clauses.append(forbid_assignment(variables, keys, bits))
            origins.append(("five", subset, bits))

    return all_triples, clauses, origins


def semantic_clause_proof(
    kind: str, vertices: tuple[int, ...], bits: tuple[bool, ...]
) -> str:
    targets = ["Turn.left" if bit else "Turn.right" for bit in bits]
    if kind == "quad":
        a, b, c, d = vertices
        named = " ".join(
            f"({name} := {target})" for name, target in zip("ABCD", targets)
        )
        return f'''(by
      have hm := turnSequence_mismatch
        (hallowed {a} {b} {c} {d} (by decide) (by decide) (by decide))
        {named} (by simp [TurnSequenceAllowed])
      simpa only [Turn.ne_right_iff_eq_left] using hm)'''

    named = " ".join(
        f"(x{i} := {target})" for i, target in enumerate(targets)
    )
    vector = ", ".join(map(str, vertices))
    return f'''(by
      let f : Fin 5 ↪o Fin 9 := OrderEmbedding.ofStrictMono ![{vector}] (by decide)
      have hm := strongFive_mismatch χ f (hno f) {named} (by simp [StrongFiveValues])
      simpa only [f, Turn.ne_right_iff_eq_left] using hm)'''


def bad_clause_contradiction(proof: str, clause: list[int]) -> str:
    bad_names = ", ".join(f"hb{i}" for i in range(len(clause)))
    cases = " | ".join("hs" for _ in clause)
    contradictions = "\n".join(
        f"      · exact "
        f"{'hb' + str(i) + ' hs' if lit > 0 else 'hs hb' + str(i)}"
        for i, lit in enumerate(clause)
    )
    return (
        f"(by\n      intro hbad\n      have hsat := {proof}\n"
        f"      rcases hbad with ⟨{bad_names}⟩\n"
        f"      rcases hsat with {cases}\n{contradictions})"
    )


def write_lean_modules(
    output: Path,
    all_triples: list[tuple[int, int, int]],
    clauses: list[list[int]],
    origins: list[tuple[str, tuple[int, ...], tuple[bool, ...]]],
) -> None:
    def triple_term(index: int) -> str:
        a, b, c = all_triples[index]
        return f"(χ ⟨{a}, {b}, {c}, by decide, by decide⟩ = Turn.left)"

    bad_clause_props = []
    for clause in clauses:
        bad_literals = [
            f"¬{triple_term(abs(lit) - 1)}" if lit > 0
            else triple_term(abs(lit) - 1)
            for lit in clause
        ]
        bad_clause_props.append("(" + " ∧ ".join(bad_literals) + ")")

    chunk_size = 126
    bad_prop_chunks = [
        bad_clause_props[start : start + chunk_size]
        for start in range(0, len(bad_clause_props), chunk_size)
    ]
    bad_chunk_definitions = "\n\n".join(
        f"def ES5BadChunk{i} (χ : TripleColoring 9) : Prop :=\n    "
        + balanced_join(chunk, "∨")
        for i, chunk in enumerate(bad_prop_chunks)
    )
    bad_disjunction = balanced_join(
        [f"ES5BadChunk{i} χ" for i in range(len(bad_prop_chunks))], "∨"
    )

    clause_proofs = [
        semantic_clause_proof(kind, vertices, bits)
        for kind, vertices, bits in origins
    ]
    bad_clause_proofs = [
        bad_clause_contradiction(proof, clause)
        for proof, clause in zip(clause_proofs, clauses)
    ]
    bad_proof_chunks = [
        bad_clause_proofs[start : start + chunk_size]
        for start in range(0, len(bad_clause_proofs), chunk_size)
    ]

    assumptions = '''(hallowed : ∀ (a b c d : Fin 9),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 5 ↪o Fin 9, ¬ IsStrongPolygonOn χ f)'''
    chunk_theorems = [
        f"theorem es5CNFChunk{i}_of_signotope_noStrong (χ : TripleColoring 9)\n"
        f"    {assumptions} : ¬ ES5BadChunk{i} χ := by\n"
        f"  unfold ES5BadChunk{i}\n"
        f"  exact {balanced_not_or_proof(chunk)}"
        for i, chunk in enumerate(bad_proof_chunks)
    ]

    header = '''/- This file is generated by scripts/generate_es5_sat.py. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace ErdosSzekeres

'''
    definitions = (
        "import ErdosSzekeres.ES5Encoding\n\n"
        + header
        + bad_chunk_definitions
        + f"\n\ndef ES5Bad (χ : TripleColoring 9) : Prop :=\n    {bad_disjunction}"
        + "\n\ndef ES5CNF (χ : TripleColoring 9) : Prop := ¬ ES5Bad χ"
        + "\n\nend ErdosSzekeres\n"
    )
    output.with_name("ES5CNFDefs.lean").write_text(definitions, encoding="utf-8")

    # Four dependency chains bound peak memory while retaining parallel builds.
    for i, theorem_text in enumerate(chunk_theorems):
        dependency = (
            f"ErdosSzekeres.ES5CNFChunk{i - 4:02}"
            if i >= 4
            else "ErdosSzekeres.ES5CNFDefs"
        )
        source = (
            f"import {dependency}\n\n"
            + header
            + theorem_text
            + "\n\nend ErdosSzekeres\n"
        )
        output.with_name(f"ES5CNFChunk{i:02}.lean").write_text(
            source, encoding="utf-8"
        )

    chunk_imports = "\n".join(
        f"import ErdosSzekeres.ES5CNFChunk{i:02}"
        for i in range(len(chunk_theorems))
    )
    arguments = " ".join(
        f"({triple_term(i)})" for i in range(len(all_triples))
    )
    bad_names = " ".join(
        f"ES5BadChunk{i}" for i in range(len(bad_prop_chunks))
    )
    semantic_steps = "\n  ".join(
        [
            f"have h{i} := "
            f"es5CNFChunk{i}_of_signotope_noStrong χ hallowed hno"
            for i in range(len(chunk_theorems))
        ]
        + ["unfold ES5CNF ES5Bad", "tauto"]
    )
    main_source = f'''{chunk_imports}

{header}theorem es5CNF_unsat (χ : TripleColoring 9) : ¬ ES5CNF χ := by
  intro hcnf
  have hcertificate := es5_signotope_unsat {arguments}
  apply hcnf
  unfold ES5Bad {bad_names}
  exact hcertificate

theorem es5CNF_of_signotope_noStrong (χ : TripleColoring 9)
    {assumptions} : ES5CNF χ := by
  {semantic_steps}

end ErdosSzekeres
'''
    output.write_text(main_source, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--lean", type=Path)
    args = parser.parse_args()

    all_triples, clauses, origins = generate()
    lines = [f"p cnf {len(all_triples)} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    args.output.write_text("\n".join(lines) + "\n", encoding="ascii")
    if args.lean is not None:
        write_lean_modules(args.lean, all_triples, clauses, origins)
    print(
        f"variables={len(all_triples)} clauses={len(clauses)} "
        f"output={args.output}"
    )


if __name__ == "__main__":
    main()
