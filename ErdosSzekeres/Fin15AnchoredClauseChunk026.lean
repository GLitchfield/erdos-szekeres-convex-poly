module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 026. -/

theorem fin15Anchored_clause03328 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03329 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03330 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03331 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03332 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03333 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03334 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03335 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03336 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03337 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03338 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03339 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03340 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03341 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03342 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03343 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03344 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03345 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03346 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03347 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03348 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03349 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03350 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03351 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03352 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03353 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03354 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03355 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03356 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03357 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03358 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03359 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03360 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03361 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03362 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03363 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03364 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03365 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03366 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03367 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03368 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03369 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03370 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03371 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03372 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03373 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03374 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03375 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03376 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03377 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03378 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03379 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03380 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03381 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03382 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03383 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03384 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03385 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03386 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03387 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0416 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03388 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03389 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03390 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03391 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03392 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03393 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03394 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03395 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03396 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03397 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03398 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03399 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03400 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03401 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03402 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03403 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03404 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03405 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03406 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03407 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03408 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03409 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03410 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03411 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03412 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03413 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03414 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03415 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03416 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03417 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03418 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03419 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03420 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03421 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03422 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03423 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0421 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03424 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03425 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03426 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03427 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03428 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03429 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03430 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03431 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03432 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03433 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03434 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03435 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03436 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03437 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03438 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03439 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03440 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0219 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03441 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0219 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03442 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0219 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0428 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03443 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0220 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03444 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0220 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03445 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0220 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03446 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0220 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03447 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0220 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03448 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0429 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0220 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0429 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03449 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03450 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03451 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03452 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03453 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03454 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0220 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03455 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0220 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
