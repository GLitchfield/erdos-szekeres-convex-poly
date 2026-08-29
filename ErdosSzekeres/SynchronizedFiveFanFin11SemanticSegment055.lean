module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment054

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 055. -/

theorem synchronizedFiveFanFin11Semantic_clause03961 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03962 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03963 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03964 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03965 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03966 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03967 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03968 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03969 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03970 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03971 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03972 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03973 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03974 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03975 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03976 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03977 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03978 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03979 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03980 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03981 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03982 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03983 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03984 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03985 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03986 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03987 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03988 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03989 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03990 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03991 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03992 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03993 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03994 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03995 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03996 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03997 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03998 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03999 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04000 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04001 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04002 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04003 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04004 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04005 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04006 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04007 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04008 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04009 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04010 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04011 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04012 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0483 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0483 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04013 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04014 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04015 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04016 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04017 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04018 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0484 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0484 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04019 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0484 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0484 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04020 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04021 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04022 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04023 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04024 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04025 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04026 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04027 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04028 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04029 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04030 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause04031 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause04032 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

end ErdosSzekeres

end
