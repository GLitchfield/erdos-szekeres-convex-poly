module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 042. -/

theorem fin15Anchored_clause05376 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05377 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05378 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05379 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05380 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05381 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05382 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05383 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05384 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05385 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05386 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05387 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05388 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05389 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05390 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05391 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05392 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05393 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05394 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05395 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05396 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05397 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05398 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05399 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05400 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05401 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05402 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05403 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05404 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05405 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05406 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05407 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05408 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05409 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05410 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05411 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05412 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05413 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05414 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05415 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05416 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05417 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05418 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05419 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05420 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05421 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05422 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05423 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05424 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05425 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05426 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05427 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05428 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05429 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05430 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05431 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0313 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05432 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0313 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05433 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0313 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05434 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0313 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05435 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05436 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05437 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05438 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05439 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05440 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05441 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05442 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05443 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05444 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05445 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05446 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05447 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05448 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05449 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05450 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05451 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05452 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05453 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05454 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05455 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05456 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05457 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05458 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05459 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05460 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05461 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05462 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05463 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05464 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05465 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05466 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05467 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05468 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05469 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05470 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05471 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05472 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05473 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05474 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05475 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05476 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05477 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05478 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05479 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05480 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05481 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05482 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05483 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05484 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05485 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05486 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05487 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05488 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05489 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05490 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05491 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05492 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05493 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05494 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05495 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05496 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05497 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05498 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05499 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05500 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05501 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05502 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05503 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
