module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 046. -/

theorem fin15Anchored_clause05888 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05889 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05890 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05891 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05892 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05893 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05894 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05895 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05896 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05897 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05898 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05899 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05900 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05901 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05902 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05903 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05904 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05905 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05906 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05907 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05908 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05909 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05910 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05911 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05912 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05913 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05914 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05915 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05916 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05917 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05918 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05919 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05920 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05921 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05922 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05923 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05924 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05925 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05926 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05927 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05928 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05929 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05930 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05931 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05932 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05933 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05934 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05935 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05936 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05937 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05938 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05939 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05940 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05941 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05942 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05943 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05944 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05945 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05946 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05947 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05948 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05949 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05950 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05951 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05952 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05953 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05954 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05955 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05956 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05957 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05958 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05959 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05960 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05961 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05962 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05963 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05964 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05965 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05966 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05967 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05968 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05969 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05970 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05971 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0349 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05972 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05973 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05974 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05975 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05976 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05977 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05978 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05979 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0350 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05980 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05981 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05982 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05983 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05984 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05985 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05986 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05987 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0347 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05988 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05989 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05990 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05991 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05992 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05993 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05994 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05995 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0348 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05996 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05997 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05998 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05999 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06000 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06001 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06002 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06003 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0349 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06004 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06005 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06006 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06007 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06008 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06009 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06010 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06011 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0346 Fin15AnchoredAtom0350 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06012 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06013 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06014 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06015 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0347 Fin15AnchoredAtom0348 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
