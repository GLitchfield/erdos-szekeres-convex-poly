module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment000

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 001. -/

theorem synchronizedFiveFanFin11Semantic_clause00073 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00074 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00075 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00076 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00077 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00078 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00079 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00080 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00081 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00082 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00083 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00084 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00085 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00086 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00087 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00088 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0172 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0172 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00089 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00090 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00091 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00092 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00093 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00094 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00095 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00096 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 2) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00097 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00098 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00099 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00100 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00101 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00102 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00103 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0001 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0173 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0001 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0173 at hbad
  cases hcolor0 : chi ⟨0, 1, 2, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00104 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00105 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00106 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00107 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00108 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00109 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00110 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00111 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0018 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0174 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0018 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0174 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00112 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00113 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00114 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00115 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00116 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00117 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00118 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00119 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0175 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0175 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00120 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00121 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00122 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00123 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00124 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00125 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00126 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00127 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0176 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0176 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00128 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0057 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00129 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00130 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0057 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00131 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00132 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00133 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00134 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0021 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0177 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0021 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0177 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00135 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00136 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00137 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00138 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00139 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00140 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00141 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00142 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0178 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0178 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause00143 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause00144 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0002 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 1) (k := 3) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0002 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  cases hcolor0 : chi ⟨0, 1, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

end ErdosSzekeres

end
