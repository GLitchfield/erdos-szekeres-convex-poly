#!/usr/bin/env python3
"""Generate the checked Lean bridge for the two Fin-17 extreme-exchange cores.

The LRAT files certify only dense propositional CNFs.  This generator
independently reconstructs the origin of every retained original clause,
checks both clause and variable maps, and emits a semantic proof for each
retained clause.  Dense variables are represented by short named atoms so the
final LRAT instantiation never unfolds all geometric propositions at once.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator


N = 17
TRIPLE_COUNT = 680
PREFIX = "ExtremeExchangeK9"


@dataclass(frozen=True)
class Orientation:
    tag: str
    source_tag: str
    small: tuple[int, ...]
    big: tuple[int, ...]
    core: tuple[int, ...]
    expected_cnf_sha256: str
    expected_lrat_sha256: str
    expected_variables: int
    expected_clauses: int
    expected_additions: int
    expected_families: dict[str, int]
    chunks: int

    @property
    def exchange_points(self) -> tuple[int, int]:
        return self.small[0], self.small[-1]


ORIENTATIONS = (
    Orientation(
        tag="89",
        source_tag="8-9",
        small=tuple(range(8)),
        big=tuple(range(8, 17)),
        core=tuple(range(8, 16)),
        expected_cnf_sha256="d9d6ed10abe6c079a090a0bc77af4533c5836f9c4ea75e847e62133694688856",
        expected_lrat_sha256="528443c8674348d9cc72154d855d4632b8482104559a0c1186ea8feae125f6cc",
        expected_variables=1811,
        expected_clauses=2141,
        expected_additions=1347,
        expected_families={
            "signotope": 524,
            "equality": 1452,
            "no_cap_four": 19,
            "no_strong_ten": 4,
            "unit": 140,
            "exchange": 2,
        },
        chunks=32,
    ),
    Orientation(
        tag="98",
        source_tag="9-8",
        small=tuple(range(9, 17)),
        big=tuple(range(9)),
        core=tuple(range(1, 9)),
        expected_cnf_sha256="29d3c1eca4838077f6f5ca2b20c1ba4d0662fdb28804f8de0f2a0048c3b9dc75",
        expected_lrat_sha256="b7960e8676216575de8bde9a1e68eeaeac3a257fc475e11039008831b8ffc929",
        expected_variables=1318,
        expected_clauses=1450,
        expected_additions=920,
        expected_families={
            "signotope": 269,
            "equality": 1030,
            "no_cap_four": 6,
            "no_strong_ten": 3,
            "unit": 140,
            "exchange": 2,
        },
        chunks=16,
    ),
)


@dataclass(frozen=True)
class Origin:
    kind: str
    vertices: tuple[int, ...]
    values: tuple[bool, ...] = ()
    side: str = ""
    equality_side: int = -1
    equality_clause: int = -1


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


def triples(vertices) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(vertices, 3))


ALL_TRIPLES = triples(range(N))
ALL_QUADS = tuple(itertools.combinations(range(N), 4))
TRIPLE_VARIABLE = {triple: index + 1 for index, triple in enumerate(ALL_TRIPLES)}


def forbidden_assignment(
    keys: tuple[tuple[int, int, int], ...], values: tuple[bool, ...]
) -> tuple[int, ...]:
    return tuple(
        -TRIPLE_VARIABLE[key] if value else TRIPLE_VARIABLE[key]
        for key, value in zip(keys, values)
    )


def equality_pairs(vertices: tuple[int, int, int, int]):
    a, b, c, d = vertices
    return (((a, b, c), (a, b, d)), ((a, c, d), (b, c, d)))


def source_clauses(orientation: Orientation) -> Iterator[tuple[tuple[int, ...], Origin]]:
    for vertices in ALL_QUADS:
        keys = tuple(itertools.combinations(vertices, 3))
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                values_tuple = tuple(values)
                yield forbidden_assignment(keys, values_tuple), Origin(
                    "signotope", vertices, values_tuple
                )

    next_variable = len(ALL_TRIPLES) + 1
    for vertices in ALL_QUADS:
        for side, (left, right) in enumerate(equality_pairs(vertices)):
            x = TRIPLE_VARIABLE[left]
            y = TRIPLE_VARIABLE[right]
            e = next_variable
            clauses = ((-e, -x, y), (-e, x, -y), (e, x, y), (e, -x, -y))
            for clause_index, clause in enumerate(clauses):
                yield clause, Origin(
                    "equality",
                    vertices,
                    equality_side=side,
                    equality_clause=clause_index,
                )
            next_variable += 1

    for vertices in ALL_QUADS:
        yield tuple(TRIPLE_VARIABLE[key] for key in triples(vertices)), Origin(
            "no_cap_four", vertices
        )

    equality_variable: dict[tuple[tuple[int, int, int, int], int], int] = {}
    next_variable = len(ALL_TRIPLES) + 1
    for vertices in ALL_QUADS:
        for side in range(2):
            equality_variable[vertices, side] = next_variable
            next_variable += 1
    for vertices in itertools.combinations(range(N), 10):
        clause: list[int] = []
        for quad in itertools.combinations(vertices, 4):
            clause.extend((-equality_variable[quad, 0], -equality_variable[quad, 1]))
        yield tuple(clause), Origin("no_strong_ten", vertices)

    for side, block in (("small", orientation.small), ("big", orientation.big)):
        for triple in triples(block):
            yield (TRIPLE_VARIABLE[triple],), Origin("unit", triple, side=side)

    for point in orientation.small:
        candidate = tuple(sorted((*orientation.core, point)))
        yield tuple(-TRIPLE_VARIABLE[key] for key in triples(candidate)), Origin(
            "exchange", candidate
        )


def parse_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = None
    declared = None
    clauses: list[tuple[int, ...]] = []
    current: list[int] = []
    for line_number, text in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        text = text.strip()
        if not text or text.startswith("c"):
            continue
        if text.startswith("p"):
            fields = text.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"] or variables is not None:
                raise ValueError(f"{path}:{line_number}: malformed CNF header")
            variables, declared = int(fields[2]), int(fields[3])
            continue
        if variables is None:
            raise ValueError(f"{path}:{line_number}: clause before header")
        for field in text.split():
            literal = int(field)
            if literal == 0:
                clauses.append(tuple(current))
                current = []
            else:
                if abs(literal) > variables:
                    raise ValueError(f"{path}:{line_number}: literal out of range")
                current.append(literal)
    if variables is None or declared is None or current or len(clauses) != declared:
        raise ValueError(f"{path}: inconsistent CNF")
    return variables, clauses


def retained_clauses(
    run_dir: Path, orientation: Orientation
) -> tuple[list[int], list[tuple[int, ...]], list[Origin]]:
    dense_path = run_dir / f"extreme-exchange-{orientation.source_tag}-dense.cnf"
    lrat_path = run_dir / f"extreme-exchange-{orientation.source_tag}-dense.lrat"
    core_map_path = run_dir / f"extreme-exchange-{orientation.source_tag}-core-map.json"
    dense_map_path = run_dir / f"extreme-exchange-{orientation.source_tag}-dense-map.json"
    if sha256(dense_path) != orientation.expected_cnf_sha256:
        raise ValueError(f"{orientation.tag}: frozen dense CNF hash mismatch")
    if sha256(lrat_path) != orientation.expected_lrat_sha256:
        raise ValueError(f"{orientation.tag}: frozen dense LRAT hash mismatch")

    core_map = json.loads(core_map_path.read_text())
    dense_map = json.loads(dense_map_path.read_text())
    old_variables = list(dense_map["old_variable_ids"])
    dense_variables, dense_clauses = parse_dimacs(dense_path)
    old_clause_ids = list(core_map["old_original_clause_ids"])
    if dense_variables != orientation.expected_variables or dense_variables != len(old_variables):
        raise ValueError(f"{orientation.tag}: dense variable count mismatch")
    if len(dense_clauses) != orientation.expected_clauses:
        raise ValueError(f"{orientation.tag}: dense clause count mismatch")
    if len(dense_clauses) != len(old_clause_ids):
        raise ValueError(f"{orientation.tag}: clause map length mismatch")
    if dense_map["dense_cnf_sha256"] != orientation.expected_cnf_sha256:
        raise ValueError(f"{orientation.tag}: dense map CNF hash mismatch")
    if dense_map["dense_lrat_sha256"] != orientation.expected_lrat_sha256:
        raise ValueError(f"{orientation.tag}: dense map LRAT hash mismatch")
    if dense_map["source_cnf_sha256"] != core_map["core_cnf_sha256"]:
        raise ValueError(f"{orientation.tag}: dense/core CNF linkage mismatch")
    if dense_map["source_lrat_sha256"] != core_map["core_lrat_sha256"]:
        raise ValueError(f"{orientation.tag}: dense/core LRAT linkage mismatch")

    wanted = set(old_clause_ids)
    found: dict[int, tuple[tuple[int, ...], Origin]] = {}
    source_count = 0
    for clause_id, item in enumerate(source_clauses(orientation), 1):
        source_count = clause_id
        if clause_id in wanted:
            found[clause_id] = item
    if source_count != 60056 or core_map["source_original_clauses"] != source_count:
        raise ValueError(f"{orientation.tag}: source clause count mismatch")
    if found.keys() != wanted:
        raise ValueError(f"{orientation.tag}: missing retained source clause")

    origins: list[Origin] = []
    for dense_clause, old_clause_id in zip(dense_clauses, old_clause_ids):
        old_clause = tuple(
            (1 if literal > 0 else -1) * old_variables[abs(literal) - 1]
            for literal in dense_clause
        )
        expected_clause, origin = found[old_clause_id]
        if old_clause != expected_clause:
            raise ValueError(
                f"{orientation.tag}: dense/source mismatch at original clause {old_clause_id}"
            )
        origins.append(origin)
    counts = Counter(origin.kind for origin in origins)
    if dict(counts) != orientation.expected_families:
        raise ValueError(f"{orientation.tag}: retained family counts differ: {dict(counts)}")
    retained_exchange = tuple(
        origin.vertices[0] if orientation.tag == "89" else origin.vertices[-1]
        for origin in origins
        if origin.kind == "exchange"
    )
    if retained_exchange != orientation.exchange_points:
        raise ValueError(f"{orientation.tag}: unexpected retained exchange clauses")
    return old_variables, dense_clauses, origins


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


def balanced_chunks(items: list[str], count: int) -> list[list[str]]:
    if count == 1:
        return [items]
    if count <= 0 or count > len(items) or count % 2:
        raise ValueError("chunk count must form a binary split tree")
    midpoint = len(items) // 2
    return balanced_chunks(items[:midpoint], count // 2) + balanced_chunks(
        items[midpoint:], count // 2
    )


def set_literal(vertices: tuple[int, ...]) -> str:
    return "{" + ", ".join(map(str, vertices)) + "}"


def vector_literal(vertices: tuple[int, ...]) -> str:
    return ", ".join(map(str, vertices))


def selected_triple_term(size: int, triple: tuple[int, int, int]) -> str:
    i, j, k = triple
    return (
        f"(χ ⟨f {i}, f {j}, f {k}, f.strictMono (by decide), "
        "f.strictMono (by decide)⟩)"
    )


def triple_term(triple: tuple[int, int, int]) -> str:
    i, j, k = triple
    return f"χ ⟨{i}, {j}, {k}, by decide, by decide⟩"


def equality_terms(old_variable: int) -> tuple[str, str]:
    offset = old_variable - TRIPLE_COUNT - 1
    if offset < 0:
        raise ValueError("not an equality variable")
    quad = ALL_QUADS[offset // 2]
    side = offset % 2
    left, right = equality_pairs(quad)[side]
    return triple_term(left), triple_term(right)


def atom_name(orientation: Orientation, dense_index: int) -> str:
    return f"{PREFIX}Dense{orientation.tag}Atom{dense_index:04}"


def atom_term(orientation: Orientation, dense_index: int) -> str:
    return f"{atom_name(orientation, dense_index)} χ"


def atom_definition(orientation: Orientation, dense_index: int, old_variable: int) -> str:
    name = atom_name(orientation, dense_index)
    if old_variable <= TRIPLE_COUNT:
        value = f"({triple_term(ALL_TRIPLES[old_variable - 1])} = Turn.left)"
    else:
        left, right = equality_terms(old_variable)
        value = f"({left} = {right})"
    return f"def {name} (χ : TripleColoring 17) : Prop := {value}"


def exchange_name(orientation: Orientation, which: str) -> str:
    return f"{PREFIX}Exchange{orientation.tag}{which}"


def exchange_vertices(orientation: Orientation, point: int) -> tuple[int, ...]:
    return tuple(sorted((*orientation.core, point)))


def mismatch_theorem(name: str, size: int, predicate: str, target: str) -> str:
    local = triples(range(size))
    actual = [selected_triple_term(size, triple) for triple in local]
    conclusion = " ∨\n    ".join(f"{term} ≠ Turn.{target}" for term in actual)
    hypotheses = ", ".join(f"h{index}" for index in range(len(local)))
    return f'''theorem {name} {{n : ℕ}} (χ : TripleColoring n)
    (f : Fin {size} ↪o Fin n) (hnot : ¬ {predicate} χ f) :
    {conclusion} := by
  by_contra h
  push Not at h
  rcases h with ⟨{hypotheses}⟩
  apply hnot
  refine ⟨f.strictMono, ?_⟩
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk <;> simp_all
'''


def strong_ten_edges() -> list[tuple[tuple[int, int, int], tuple[int, int, int]]]:
    edges: list[tuple[tuple[int, int, int], tuple[int, int, int]]] = []
    for a, b, c, d in itertools.combinations(range(10), 4):
        edges.append(((a, b, c), (a, b, d)))
        edges.append(((a, c, d), (b, c, d)))
    return edges


def strong_ten_spanning_indices() -> list[int]:
    edges = strong_ten_edges()
    term_index = {edge: index for index, edge in enumerate(edges)}
    # For every fixed middle vertex b, the triples (a,b,c) form a rectangular
    # grid.  The two equality families above are exactly the row and column
    # edges of that grid.  A spanning tree therefore needs only
    # C(10,3) - 8 = 112 of the 420 available edges.  Case-splitting on those
    # edges is dramatically cheaper for Lean than expanding all 420 negations.
    selected: list[int] = []
    for b in range(1, 9):
        # Connect the row a=0 to its canonical cell (0,b,b+1).
        for c in range(b + 2, 10):
            selected.append(term_index[((0, b, b + 1), (0, b, c))])
        # Connect the remaining rows at the canonical column c=b+1.
        for a in range(1, b):
            selected.append(term_index[((0, b, b + 1), (a, b, b + 1))])
        # Connect every remaining cell to its row's canonical cell.
        for a in range(1, b):
            for c in range(b + 2, 10):
                selected.append(term_index[((a, b, b + 1), (a, b, c))])
    if len(selected) != 112 or len(set(selected)) != len(selected):
        raise AssertionError("strong-ten spanning tree must have 112 distinct edges")
    return selected


def balanced_and_pattern(items: list[str]) -> str:
    if len(items) == 1:
        return items[0]
    midpoint = len(items) // 2
    return (
        f"⟨{balanced_and_pattern(items[:midpoint])}, "
        f"{balanced_and_pattern(items[midpoint:])}⟩"
    )


def balanced_and_projection(root: str, position: int, length: int) -> str:
    """Project one leaf from the same midpoint-balanced conjunction as balanced_join."""
    if length <= 0 or position < 0 or position >= length:
        raise ValueError("balanced conjunction projection is out of range")
    if length == 1:
        return root
    midpoint = length // 2
    if position < midpoint:
        return balanced_and_projection(f"{root}.1", position, midpoint)
    return balanced_and_projection(f"{root}.2", position - midpoint, length - midpoint)


def fixed_chunks(
    items: list[tuple[int, int, int]], size: int
) -> list[list[tuple[int, int, int]]]:
    if size < 1:
        raise ValueError("fixed chunk size must be positive")
    return [items[index:index + size] for index in range(0, len(items), size)]


def write_encoding(repo: Path) -> None:
    exchange_defs: list[str] = []
    for orientation in ORIENTATIONS:
        for which, point in zip(("First", "Last"), orientation.exchange_points):
            vertices = exchange_vertices(orientation, point)
            exchange_defs.append(
                f"def {exchange_name(orientation, which)} : Fin 9 ↪o Fin 17 :=\n"
                f"  OrderEmbedding.ofStrictMono ![{vector_literal(vertices)}] (by decide)"
            )
    source = f'''module

public import ErdosSzekeres.StructuralChargingPascalCupBlocks

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ErdosSzekeres

noncomputable section

{mismatch_theorem("extremeExchangeK9_capFour_mismatch", 4, "IsCap", "right")}

{mismatch_theorem("extremeExchangeK9_cupNine_mismatch", 9, "IsCup", "left")}

theorem extremeExchangeK9_eqDef0 (x y : Turn) :
    ¬(x = y) ∨ ¬(x = Turn.left) ∨ y = Turn.left := by
  cases x <;> cases y <;> simp

theorem extremeExchangeK9_eqDef1 (x y : Turn) :
    ¬(x = y) ∨ x = Turn.left ∨ ¬(y = Turn.left) := by
  cases x <;> cases y <;> simp

theorem extremeExchangeK9_eqDef2 (x y : Turn) :
    x = y ∨ x = Turn.left ∨ y = Turn.left := by
  cases x <;> cases y <;> simp

theorem extremeExchangeK9_eqDef3 (x y : Turn) :
    x = y ∨ ¬(x = Turn.left) ∨ ¬(y = Turn.left) := by
  cases x <;> cases y <;> simp

{chr(10).join(exchange_defs)}

end


end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Encoding.lean", source)

    strong_source = f'''module

public import ErdosSzekeres.{PREFIX}Encoding

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ErdosSzekeres

noncomputable section

/- The 420-literal strong-ten clauses are discharged directly from their
   balanced bad-clause conjunctions in the semantic chunk modules.  Keeping
   this import boundary makes the generated module graph stable. -/

end


end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}StrongEncoding.lean", strong_source)


def write_unsat(repo: Path, run_dir: Path, orientation: Orientation) -> None:
    source_cnf = run_dir / f"extreme-exchange-{orientation.source_tag}-dense.cnf"
    source_lrat = run_dir / f"extreme-exchange-{orientation.source_tag}-dense.lrat"
    target_stem = f"extreme-exchange-k9-{orientation.source_tag}-dense"
    write_if_changed(repo / "certificates" / f"{target_stem}.cnf", source_cnf.read_bytes())
    write_if_changed(repo / "certificates" / f"{target_stem}.lrat", source_lrat.read_bytes())
    source = f'''module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT proof for the dense `{orientation.source_tag}` extreme-exchange core. -/

namespace ErdosSzekeres

lrat_proof extremeExchangeK9Dense{orientation.tag}_lrat_unsat
  (include_str "../certificates/{target_stem}.cnf")
  (include_str "../certificates/{target_stem}.lrat")

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Dense{orientation.tag}Unsat.lean", source)


def write_atoms(repo: Path, orientation: Orientation, old_variables: list[int]) -> None:
    definitions = "\n\n".join(
        atom_definition(orientation, index, old_variable)
        for index, old_variable in enumerate(old_variables)
    )
    source = f'''module

public import ErdosSzekeres.{PREFIX}StrongEncoding

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

namespace ErdosSzekeres

{definitions}

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Dense{orientation.tag}Atoms.lean", source)


def turn_term(value: bool) -> str:
    return "Turn.left" if value else "Turn.right"


def assumptions(orientation: Orientation) -> str:
    return f'''(hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩))
    (hnoCap : ∀ f : Fin 4 ↪o Fin 17, ¬ IsCap χ f)
    (hnoStrong : ∀ f : Fin 10 ↪o Fin 17, ¬ IsStrongPolygonOn χ f)
    (hsmall : IsCupSet χ {set_literal(orientation.small)})
    (hbig : IsCupSet χ {set_literal(orientation.big)})
    (hnoFirst : ¬ IsCup χ {exchange_name(orientation, "First")})
    (hnoLast : ¬ IsCup χ {exchange_name(orientation, "Last")})'''


def semantic_clause_proof(
    orientation: Orientation, clause: tuple[int, ...], origin: Origin
) -> str:
    names = [atom_name(orientation, abs(literal) - 1) for literal in clause]
    unfolds = ", ".join(dict.fromkeys(names))
    if origin.kind == "signotope":
        a, b, c, d = origin.vertices
        named = " ".join(
            f"({name} := {turn_term(value)})"
            for name, value in zip("ABCD", origin.values)
        )
        return f'''(by
      have hm := turnSequence_mismatch
        (hallowed {a} {b} {c} {d} (by decide) (by decide) (by decide))
        {named} (by simp [TurnSequenceAllowed])
      simpa only [{unfolds}, Turn.ne_right_iff_eq_left] using hm)'''
    if origin.kind == "equality":
        old_equality = (
            TRIPLE_COUNT
            + 1
            + 2 * ALL_QUADS.index(origin.vertices)
            + origin.equality_side
        )
        left, right = equality_terms(old_equality)
        theorem = f"extremeExchangeK9_eqDef{origin.equality_clause}"
        return f'''(by
      simpa only [{unfolds}] using {theorem} ({left}) ({right}))'''
    if origin.kind == "no_cap_four":
        vector = vector_literal(origin.vertices)
        return f'''(by
      let f : Fin 4 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![{vector}] (by decide)
      have hm := extremeExchangeK9_capFour_mismatch χ f (hnoCap f)
      simpa only [f, {unfolds}, Turn.ne_right_iff_eq_left] using hm)'''
    if origin.kind == "no_strong_ten":
        vector = vector_literal(origin.vertices)
        return f'''(by
      let f : Fin 10 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![{vector}] (by decide)
      have hm := extremeExchangeK9_strongTen_mismatch χ f (hnoStrong f)
      simpa only [f, {unfolds}] using hm)'''
    if origin.kind == "unit":
        i, j, k = origin.vertices
        hypothesis = "hsmall" if origin.side == "small" else "hbig"
        return f'''(by
      simpa only [{unfolds}] using {hypothesis} ⟨{i}, {j}, {k}, by decide, by decide⟩
        (by simp) (by simp) (by simp))'''
    if origin.kind == "exchange":
        point = origin.vertices[0] if orientation.tag == "89" else origin.vertices[-1]
        which = "First" if point == orientation.exchange_points[0] else "Last"
        hypothesis = "hnoFirst" if which == "First" else "hnoLast"
        exchange = exchange_name(orientation, which)
        return f'''(by
      have hm := extremeExchangeK9_cupNine_mismatch χ {exchange} {hypothesis}
      simpa only [{exchange}, {unfolds}] using hm)'''
    raise ValueError(origin.kind)


def bad_clause_contradiction(proof: str, clause: tuple[int, ...]) -> str:
    if len(clause) == 1:
        contradiction = "hbad hsat" if clause[0] > 0 else "hsat hbad"
        return f"(by\n      intro hbad\n      have hsat := {proof}\n      exact {contradiction})"
    names = [f"hb{index}" for index in range(len(clause))]
    bad_pattern = balanced_and_pattern(names)
    cases = " | ".join("hs" for _ in clause)
    contradictions = "\n".join(
        f"      · exact {'hb' + str(index) + ' hs' if literal > 0 else 'hs hb' + str(index)}"
        for index, literal in enumerate(clause)
    )
    return f'''(by
      intro hbad
      have hsat := {proof}
      rcases hbad with {bad_pattern}
      rcases hsat with {cases}
{contradictions})'''


def strong_clause_selected_positions(
    orientation: Orientation,
    old_variables: list[int],
    clause: tuple[int, ...],
    origin: Origin,
) -> tuple[list[int], dict[int, int]]:
    if len(clause) != 420:
        raise ValueError("no-strong-ten clause must retain all 420 equality literals")
    selected = strong_ten_spanning_indices()
    local_quads = list(itertools.combinations(range(10), 4))
    expected_old: list[int] = []
    for edge_index in selected:
        local_quad = local_quads[edge_index // 2]
        actual_quad = tuple(origin.vertices[index] for index in local_quad)
        expected_old.append(
            TRIPLE_COUNT + 1 + 2 * ALL_QUADS.index(actual_quad) + edge_index % 2
        )
    clause_old = [old_variables[abs(literal) - 1] for literal in clause]
    selected_positions: list[int] = []
    for old_variable in expected_old:
        try:
            position = clause_old.index(old_variable)
        except ValueError as error:
            raise ValueError("spanning equality missing from no-strong-ten clause") from error
        if clause[position] >= 0:
            raise ValueError("no-strong-ten equality literal must be negative")
        selected_positions.append(position)
    if len(set(selected_positions)) != 112:
        raise ValueError("no-strong-ten selected clause positions are not distinct")
    return selected_positions, dict(zip(selected, selected_positions))


def mapped_triple_term(
    vertices: tuple[int, ...], triple: tuple[int, int, int]
) -> str:
    return triple_term(tuple(vertices[index] for index in triple))


def embedded_triple_term(embedding: str, triple: tuple[int, int, int]) -> str:
    first, middle, last = triple
    return (
        f"χ ⟨{embedding} {first}, {embedding} {middle}, {embedding} {last}, "
        f"{embedding}.strictMono (by decide), {embedding}.strictMono (by decide)⟩"
    )


def middle_fact_term(
    embedding: str, triple: tuple[int, int, int]
) -> str:
    _, middle, _ = triple
    canonical = (0, middle, middle + 1)
    return (
        f"({embedded_triple_term(embedding, triple)}) = "
        f"({embedded_triple_term(embedding, canonical)})"
    )


def middle_fact_proof(
    orientation: Orientation,
    clause: tuple[int, ...],
    triple: tuple[int, int, int],
    edge_position: dict[int, int],
    embedding: str,
) -> str:
    edges = strong_ten_edges()
    edge_index = {edge: index for index, edge in enumerate(edges)}
    first, middle, last = triple
    canonical = (0, middle, middle + 1)
    if triple == canonical:
        return "rfl"
    if first == 0 or last == middle + 1:
        position = edge_position[edge_index[(canonical, triple)]]
        projection = balanced_and_projection("hbad", position, len(clause))
        source = f"({projection}).symm"
        atoms = [atom_name(orientation, abs(clause[position]) - 1)]
    else:
        row_canonical = (first, middle, middle + 1)
        column_position = edge_position[edge_index[(canonical, row_canonical)]]
        row_position = edge_position[edge_index[(row_canonical, triple)]]
        column = balanced_and_projection("hbad", column_position, len(clause))
        row = balanced_and_projection("hbad", row_position, len(clause))
        source = f"({row}).symm.trans ({column}).symm"
        atoms = [
            atom_name(orientation, abs(clause[row_position]) - 1),
            atom_name(orientation, abs(clause[column_position]) - 1),
        ]
    return f"by simpa only [{embedding}, {', '.join(atoms)}] using {source}"


def write_strong_pattern(repo: Path) -> None:
    source = f'''module

public import ErdosSzekeres.{PREFIX}Encoding

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

namespace ErdosSzekeres

theorem extremeExchangeK9_isStrongPolygonOn_of_middle_color
    (χ : TripleColoring 17) (f : Fin 10 ↪o Fin 17) (color : Fin 10 → Turn)
    (hmiddle : ∀ (i j k : Fin 10), (hij : i < j) → (hjk : j < k) →
      χ ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩ = color j) :
    IsStrongPolygonOn χ f := by
  intro i j k l hij hjk hkl
  exact ⟨
    (hmiddle i j k hij hjk).trans
      (hmiddle i j l hij (hjk.trans hkl)).symm,
    (hmiddle i k l (hij.trans hjk) hkl).trans
      (hmiddle j k l hjk hkl).symm⟩

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}StrongClausePattern.lean", source)


def write_strong_clause_modules(
    repo: Path,
    orientation: Orientation,
    old_variables: list[int],
    clause: tuple[int, ...],
    origin: Origin,
    clause_index: int,
) -> dict[str, object]:
    selected_positions, edge_position = strong_clause_selected_positions(
        orientation, old_variables, clause, origin
    )
    literals = [
        f"¬{atom_term(orientation, abs(literal) - 1)}"
        if literal > 0
        else atom_term(orientation, abs(literal) - 1)
        for literal in clause
    ]
    bad_prop = balanced_join(literals, "∧")
    clause_tag = f"{orientation.tag}Clause{clause_index:02}"
    base_name = f"{PREFIX}StrongClause{clause_tag}"
    bad_name = f"{base_name}Bad"
    embedding_name = f"{base_name}Embedding"
    lean_dir = repo / "ErdosSzekeres"
    base_source = f'''module

public import ErdosSzekeres.{PREFIX}Dense{orientation.tag}Atoms

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

set_option maxRecDepth 30000

namespace ErdosSzekeres

def {embedding_name} : Fin 10 ↪o Fin 17 :=
  OrderEmbedding.ofStrictMono ![{vector_literal(origin.vertices)}] (by decide)

def {bad_name} (χ : TripleColoring 17) : Prop :=
  {bad_prop}

end ErdosSzekeres

end
'''
    write_if_changed(lean_dir / f"{base_name}.lean", base_source)

    all_triples = list(itertools.combinations(range(10), 3))
    fact_chunks = fixed_chunks(all_triples, 15)
    fact_names: list[str] = []
    chunk_names: list[str] = []
    for chunk_index, chunk in enumerate(fact_chunks):
        chunk_name = f"{PREFIX}MiddleFacts{clause_tag}Chunk{chunk_index:02}"
        chunk_names.append(chunk_name)
        facts = [middle_fact_term(embedding_name, triple) for triple in chunk]
        proofs = [
            middle_fact_proof(
                orientation, clause, triple, edge_position, embedding_name
            )
            for triple in chunk
        ]
        fact_names.extend(f"hm{a}{b}{c}" for a, b, c in chunk)
        chunk_source = f'''module

public import ErdosSzekeres.{base_name}

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

set_option maxRecDepth 30000

namespace ErdosSzekeres

theorem {chunk_name}_of_bad (χ : TripleColoring 17) (hbad : {bad_name} χ) :
    {balanced_join(facts, "∧")} := by
  unfold {bad_name} at hbad
  exact {balanced_and_pattern(proofs)}

end ErdosSzekeres

end
'''
        write_if_changed(lean_dir / f"{chunk_name}.lean", chunk_source)

    imports = "\n".join(
        f"public import ErdosSzekeres.{chunk_name}" for chunk_name in chunk_names
    )
    extracts: list[str] = []
    total_facts = 0
    for chunk_name, chunk in zip(chunk_names, fact_chunks):
        names = [f"hm{a}{b}{c}" for a, b, c in chunk]
        extracts.append(
            f"  rcases {chunk_name}_of_bad χ hbad with {balanced_and_pattern(names)}"
        )
        total_facts += len(chunk)
    if total_facts != 120 or len(fact_names) != 120:
        raise AssertionError("middle-color chunks must contain exactly 120 facts")
    colors = "\n".join(
        f"  let c{middle} : Turn := "
        f"(χ ⟨{embedding_name} 0, {embedding_name} {middle}, "
        f"{embedding_name} {middle + 1}, {embedding_name}.strictMono (by decide), "
        f"{embedding_name}.strictMono (by decide)⟩)"
        for middle in range(1, 9)
    )
    color_vector = ", ".join(
        ["Turn.left", *(f"c{middle}" for middle in range(1, 9)), "Turn.left"]
    )
    helper_name = f"{PREFIX}Dense{orientation.tag}StrongClause{clause_index:02}"
    final_source = f'''module

public import ErdosSzekeres.{PREFIX}StrongClausePattern
{imports}

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace ErdosSzekeres

theorem {helper_name}_of_constraints
    (χ : TripleColoring 17)
    (hnoStrong : ∀ f : Fin 10 ↪o Fin 17, ¬ IsStrongPolygonOn χ f) :
    ¬ ({bad_prop}) := by
  intro hbad
  change {bad_name} χ at hbad
{chr(10).join(extracts)}
{colors}
  apply hnoStrong {embedding_name}
  apply extremeExchangeK9_isStrongPolygonOn_of_middle_color χ {embedding_name}
    ![{color_vector}]
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp at hij hjk <;> dsimp only [c1, c2, c3, c4, c5, c6, c7, c8] <;> assumption

end ErdosSzekeres

end
'''
    final_name = f"{base_name}Final"
    write_if_changed(lean_dir / f"{final_name}.lean", final_source)
    return {
        "orientation": orientation.tag,
        "clause_index": clause_index,
        "vertices": list(origin.vertices),
        "selected_positions": selected_positions,
        "middle_fact_chunk_sizes": [len(chunk) for chunk in fact_chunks],
        "base_module": base_name,
        "final_module": final_name,
        "helper_theorem": f"{helper_name}_of_constraints",
    }


def write_orientation_modules(
    repo: Path,
    orientation: Orientation,
    old_variables: list[int],
    clauses: list[tuple[int, ...]],
    origins: list[Origin],
    owned_paths_only: bool = False,
) -> dict[str, object]:
    if not owned_paths_only:
        write_atoms(repo, orientation, old_variables)
    bad_props: list[str] = []
    proofs: list[str] = []
    strong_helper_names: list[str] = []
    clause_helper_names: list[str | None] = []
    lean_dir = repo / "ErdosSzekeres"
    for clause, origin in zip(clauses, origins):
        literals = [
            f"¬{atom_term(orientation, abs(literal) - 1)}"
            if literal > 0
            else atom_term(orientation, abs(literal) - 1)
            for literal in clause
        ]
        bad_prop = balanced_join(literals, "∧")
        bad_props.append(bad_prop)
        if origin.kind == "no_strong_ten":
            helper_name = (
                f"{PREFIX}Dense{orientation.tag}StrongClause"
                f"{len(strong_helper_names):02}"
            )
            strong_helper_names.append(helper_name)
            write_strong_clause_modules(
                repo,
                orientation,
                old_variables,
                clause,
                origin,
                len(strong_helper_names) - 1,
            )
            proofs.append(f"({helper_name}_of_constraints χ hnoStrong)")
            clause_helper_names.append(
                f"{PREFIX}StrongClause{orientation.tag}"
                f"Clause{len(strong_helper_names) - 1:02}Final"
            )
        else:
            proofs.append(
                bad_clause_contradiction(
                    semantic_clause_proof(orientation, clause, origin), clause
                )
            )
            clause_helper_names.append(None)
    prop_chunks = balanced_chunks(bad_props, orientation.chunks)
    proof_chunks = balanced_chunks(proofs, orientation.chunks)
    helper_chunks = balanced_chunks(clause_helper_names, orientation.chunks)
    for index, (props, chunk_proofs, chunk_helpers) in enumerate(
        zip(prop_chunks, proof_chunks, helper_chunks)
    ):
        semantic_imports = "\n".join(
            f"public import ErdosSzekeres.{name}"
            for name in dict.fromkeys(name for name in chunk_helpers if name is not None)
        )
        if not semantic_imports:
            semantic_imports = (
                f"public import ErdosSzekeres.{PREFIX}Dense{orientation.tag}Atoms"
            )
        chunk_name = f"{PREFIX}Dense{orientation.tag}BadChunk{index:02}"
        source = f'''module

{semantic_imports}

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace ErdosSzekeres

def {chunk_name} (χ : TripleColoring 17) : Prop :=
  {balanced_join(props, "∨")}

theorem extremeExchangeK9Dense{orientation.tag}CNFChunk{index:02}_of_constraints
    (χ : TripleColoring 17) {assumptions(orientation)} :
    ¬ {chunk_name} χ := by
  unfold {chunk_name}
  exact {balanced_not_or_proof(chunk_proofs)}

end ErdosSzekeres

end
'''
        if owned_paths_only:
            module_name = f"{PREFIX}StrongClause{orientation.tag}CNFChunk{index:02}"
        else:
            module_name = f"{PREFIX}Dense{orientation.tag}CNFChunk{index:02}"
        write_if_changed(lean_dir / f"{module_name}.lean", source)

    if owned_paths_only:
        chunk_modules = [
            f"{PREFIX}StrongClause{orientation.tag}CNFChunk{index:02}"
            for index in range(orientation.chunks)
        ]
    else:
        chunk_modules = [
            f"{PREFIX}Dense{orientation.tag}CNFChunk{index:02}"
            for index in range(orientation.chunks)
        ]
    imports = "\n".join(
        f"public import ErdosSzekeres.{module_name}" for module_name in chunk_modules
    )
    imports += f"\npublic import ErdosSzekeres.{PREFIX}Dense{orientation.tag}Unsat"
    chunk_names = [
        f"{PREFIX}Dense{orientation.tag}BadChunk{index:02}"
        for index in range(orientation.chunks)
    ]
    bad_name = f"{PREFIX}Dense{orientation.tag}Bad"
    cnf_name = f"{PREFIX}Dense{orientation.tag}CNF"
    bad_definition = balanced_join([f"{name} χ" for name in chunk_names], "∨")
    arguments = " ".join(
        f"({atom_term(orientation, index)})" for index in range(len(old_variables))
    )
    calls = "\n  ".join(
        f"have h{index} := extremeExchangeK9Dense{orientation.tag}CNFChunk{index:02}_of_constraints "
        "χ hallowed hnoCap hnoStrong hsmall hbig hnoFirst hnoLast"
        for index in range(orientation.chunks)
    )
    root = f'''module

{imports}

@[expose] public section

/- This file is generated by scripts/generate_extreme_exchange_k9_lean.py. -/

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace ErdosSzekeres

def {bad_name} (χ : TripleColoring 17) : Prop :=
  {bad_definition}

def {cnf_name} (χ : TripleColoring 17) : Prop := ¬ {bad_name} χ

theorem extremeExchangeK9Dense{orientation.tag}CNF_unsat
    (χ : TripleColoring 17) : ¬ {cnf_name} χ := by
  intro hcnf
  have hcertificate := extremeExchangeK9Dense{orientation.tag}_lrat_unsat {arguments}
  apply hcnf
  unfold {bad_name} {' '.join(chunk_names)}
  simpa only [and_assoc] using hcertificate

theorem extremeExchangeK9Dense{orientation.tag}CNF_of_constraints
    (χ : TripleColoring 17) {assumptions(orientation)} : {cnf_name} χ := by
  {calls}
  unfold {cnf_name} {bad_name}
  tauto

end ErdosSzekeres

end
'''
    if owned_paths_only:
        root_module = f"{PREFIX}StrongClause{orientation.tag}CNFGenerated"
    else:
        root_module = f"{PREFIX}Dense{orientation.tag}CNFGenerated"
    write_if_changed(lean_dir / f"{root_module}.lean", root)
    return {
        "tag": orientation.tag,
        "source_tag": orientation.source_tag,
        "variables": len(old_variables),
        "clauses": len(clauses),
        "families": dict(Counter(origin.kind for origin in origins)),
        "cnf_sha256": orientation.expected_cnf_sha256,
        "lrat_sha256": orientation.expected_lrat_sha256,
    }


def component_definition(orientation: Orientation) -> str:
    return f'''def ExtremeExchangeK9FinSeventeen{orientation.tag} : Prop :=
  ∀ χ : TripleColoring 17,
    OneChangeOn χ Finset.univ →
      IsCupSet χ {set_literal(orientation.small)} →
        IsCupSet χ {set_literal(orientation.big)} →
          (∀ f : Fin 4 ↪o Fin 17, ¬ IsCap χ f) →
            (∀ f : Fin 10 ↪o Fin 17, ¬ IsStrongPolygonOn χ f) →
              IsCup χ {exchange_name(orientation, "First")} ∨
                IsCup χ {exchange_name(orientation, "Last")}

theorem extremeExchangeK9FinSeventeen{orientation.tag} :
    ExtremeExchangeK9FinSeventeen{orientation.tag} := by
  intro χ hone hsmall hbig hnoCap hnoStrong
  by_contra hout
  push Not at hout
  rcases hout with ⟨hnoFirst, hnoLast⟩
  have hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    exact hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  exact extremeExchangeK9Dense{orientation.tag}CNF_unsat χ
    (extremeExchangeK9Dense{orientation.tag}CNF_of_constraints χ
      hallowed hnoCap hnoStrong hsmall hbig hnoFirst hnoLast)
'''


def write_final(repo: Path, owned_roots: bool = False) -> None:
    if owned_roots:
        imports = f'''public import ErdosSzekeres.{PREFIX}StrongClause89CNFGenerated
public import ErdosSzekeres.{PREFIX}StrongClause98CNFGenerated'''
    else:
        imports = f'''public import ErdosSzekeres.{PREFIX}Dense89CNFGenerated
public import ErdosSzekeres.{PREFIX}Dense98CNFGenerated'''
    source = f'''module

{imports}

@[expose] public section

/-! Exact normalized Fin-17 consequences of the two extreme-exchange certificates. -/

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ErdosSzekeres

{component_definition(ORIENTATIONS[0])}

{component_definition(ORIENTATIONS[1])}

theorem extremeExchangeK9FinSeventeen :
    ExtremeExchangeK9FinSeventeen89 ∧ ExtremeExchangeK9FinSeventeen98 := by
  exact ⟨extremeExchangeK9FinSeventeen89, extremeExchangeK9FinSeventeen98⟩

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Certificate.lean", source)


def write_middle_only(
    repo: Path,
    run_dir: Path,
    orientation_tag: str | None,
    strong_clause: int | None,
) -> list[dict[str, object]]:
    write_strong_pattern(repo)
    audit: list[dict[str, object]] = []
    for orientation in ORIENTATIONS:
        if orientation_tag is not None and orientation.tag != orientation_tag:
            continue
        old_variables, clauses, origins = retained_clauses(run_dir, orientation)
        strong_items = [
            (clause, origin)
            for clause, origin in zip(clauses, origins)
            if origin.kind == "no_strong_ten"
        ]
        if strong_clause is not None and strong_clause >= len(strong_items):
            raise ValueError(
                f"{orientation.tag}: strong clause {strong_clause} is out of range"
            )
        for clause_index, (clause, origin) in enumerate(strong_items):
            if strong_clause is not None and clause_index != strong_clause:
                continue
            audit.append(
                write_strong_clause_modules(
                    repo, orientation, old_variables, clause, origin, clause_index
                )
            )
    return audit


def write_full_owned(repo: Path, run_dir: Path) -> list[dict[str, object]]:
    write_strong_pattern(repo)
    audit: list[dict[str, object]] = []
    for orientation in ORIENTATIONS:
        old_variables, clauses, origins = retained_clauses(run_dir, orientation)
        audit.append(
            write_orientation_modules(
                repo,
                orientation,
                old_variables,
                clauses,
                origins,
                owned_paths_only=True,
            )
        )
    write_final(repo, owned_roots=True)
    return audit


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument(
        "--source-run",
        type=Path,
        default=Path("runs/agents/20260811-wave3/extreme-exchange"),
    )
    parser.add_argument(
        "--audit-output",
        type=Path,
        default=Path("runs/agents/20260811-wave3/extreme-exchange-lean-v2/generation-audit.json"),
    )
    parser.add_argument(
        "--middle-only",
        action="store_true",
        help="write only the owned split strong-clause modules",
    )
    parser.add_argument(
        "--full-owned",
        action="store_true",
        help="write the complete bridge using only packet-owned module names",
    )
    parser.add_argument("--orientation", choices=("89", "98"))
    parser.add_argument("--strong-clause", type=int)
    args = parser.parse_args()
    repo = args.repo.resolve()
    run_dir = args.source_run if args.source_run.is_absolute() else repo / args.source_run
    if args.middle_only and args.full_owned:
        parser.error("--middle-only and --full-owned are mutually exclusive")
    if not args.middle_only and (args.orientation is not None or args.strong_clause is not None):
        parser.error("--orientation and --strong-clause require --middle-only")
    if args.strong_clause is not None and args.orientation is None:
        parser.error("--strong-clause requires --orientation")
    if args.middle_only:
        audit = write_middle_only(repo, run_dir, args.orientation, args.strong_clause)
    elif args.full_owned:
        audit = write_full_owned(repo, run_dir)
    else:
        write_encoding(repo)
        write_strong_pattern(repo)
        audit = []
        for orientation in ORIENTATIONS:
            old_variables, clauses, origins = retained_clauses(run_dir, orientation)
            write_unsat(repo, run_dir, orientation)
            audit.append(
                write_orientation_modules(repo, orientation, old_variables, clauses, origins)
            )
        write_final(repo)
    audit_path = args.audit_output if args.audit_output.is_absolute() else repo / args.audit_output
    write_if_changed(
        audit_path,
        json.dumps({"schema_version": 1, "orientations": audit}, indent=2, sort_keys=True)
        + "\n",
    )
    print(json.dumps({"status": "generated", "audit": str(audit_path)}, sort_keys=True))


if __name__ == "__main__":
    main()
