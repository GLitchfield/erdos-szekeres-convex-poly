module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 034. -/

theorem fin15Anchored_clause04352 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04353 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04354 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04355 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04356 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04357 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04358 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04359 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04360 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0261 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04361 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04362 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04363 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04364 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04365 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04366 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04367 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04368 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0262 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04369 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04370 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04371 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04372 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04373 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04374 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04375 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04376 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0259 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04377 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04378 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04379 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04380 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04381 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04382 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04383 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04384 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0260 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04385 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04386 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04387 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04388 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04389 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04390 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04391 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04392 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0261 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04393 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04394 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04395 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04396 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04397 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04398 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04399 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04400 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0258 Fin15AnchoredAtom0262 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04401 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04402 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04403 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04404 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04405 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04406 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04407 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0260 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04408 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04409 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04410 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04411 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04412 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04413 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04414 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04415 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0259 Fin15AnchoredAtom0261 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04416 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04417 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04418 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04419 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04420 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04421 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04422 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04423 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04424 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04425 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04426 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04427 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04428 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04429 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04430 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04431 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04432 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04433 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04434 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04435 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04436 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04437 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04438 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04439 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04440 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04441 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04442 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04443 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04444 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04445 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04446 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04447 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04448 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04449 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04450 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04451 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04452 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04453 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04454 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04455 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04456 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04457 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04458 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04459 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04460 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04461 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04462 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04463 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04464 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04465 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04466 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04467 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04468 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04469 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04470 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04471 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04472 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04473 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04474 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04475 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04476 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04477 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04478 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04479 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
