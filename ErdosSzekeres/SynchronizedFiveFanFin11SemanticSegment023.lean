module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment022

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 023. -/

theorem synchronizedFiveFanFin11Semantic_clause01657 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01658 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01659 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01660 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01661 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01662 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01663 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01664 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01665 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01666 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01667 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01668 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01669 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01670 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01671 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01672 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01673 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01674 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01675 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01676 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01677 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01678 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01679 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01680 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01681 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01682 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01683 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01684 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01685 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01686 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01687 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01688 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01689 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01690 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01691 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01692 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01693 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01694 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01695 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01696 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01697 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01698 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01699 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01700 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01701 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01702 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01703 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01704 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01705 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01706 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01707 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01708 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01709 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01710 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01711 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01712 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01713 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01714 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01715 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01716 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01717 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01718 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01719 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01720 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01721 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01722 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01723 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01724 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  cases hcolor0 : chi ⟨1, 2, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause01725 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01726 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01727 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 2) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause01728 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0303 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  cases hcolor0 : chi ⟨1, 2, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

end ErdosSzekeres

end
