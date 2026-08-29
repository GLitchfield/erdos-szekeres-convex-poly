module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment050

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 051. -/

theorem synchronizedFiveFanFin11Semantic_clause03673 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0162 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0162 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03674 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03675 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0163 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03676 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0454 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0163 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0454 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03677 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03678 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03679 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03680 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03681 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03682 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03683 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0164 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03684 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03685 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03686 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03687 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03688 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03689 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03690 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03691 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03692 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03693 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03694 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03695 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03696 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03697 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03698 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03699 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03700 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03701 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03702 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03703 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03704 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03705 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03706 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03707 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03708 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03709 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03710 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03711 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03712 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03713 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03714 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03715 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03716 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03717 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03718 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03719 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03720 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03721 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03722 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03723 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03724 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03725 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03726 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03727 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03728 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03729 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03730 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03731 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03732 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03733 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03734 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03735 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03736 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03737 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03738 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03739 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03740 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03741 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03742 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03743 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03744 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

end ErdosSzekeres

end
