module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment048

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 049. -/

theorem synchronizedFiveFanFin11Semantic_clause03529 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03530 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03531 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03532 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03533 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0442 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03534 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0442 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0442 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03535 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03536 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03537 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03538 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03539 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03540 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03541 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03542 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03543 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03544 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03545 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03546 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03547 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03548 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03549 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03550 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03551 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03552 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03553 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03554 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03555 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03556 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0127 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0127 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03557 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03558 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03559 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03560 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03561 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03562 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03563 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03564 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03565 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03566 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03567 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03568 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03569 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03570 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03571 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03572 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03573 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03574 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03575 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03576 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03577 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03578 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03579 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03580 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03581 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03582 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03583 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03584 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03585 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03586 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03587 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03588 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03589 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03590 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03591 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03592 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03593 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03594 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03595 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03596 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03597 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0156 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03598 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

theorem synchronizedFiveFanFin11Semantic_clause03599 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0125 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0448 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0125 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0156 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0448 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]

theorem synchronizedFiveFanFin11Semantic_clause03600 (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed]

end ErdosSzekeres

end
