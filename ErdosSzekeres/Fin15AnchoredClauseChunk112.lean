module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 112. -/

theorem fin15Anchored_clause14336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1680 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1680 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0361 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1681 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0361 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1681 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14341 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14342 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14343 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14344 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1682 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14350 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14351 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14352 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14353 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14355 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1683 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14361 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14362 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1684 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14370 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14371 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1685 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14381 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14382 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14384 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1686 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14388 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1687 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14389 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1687 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14390 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1687 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1687 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1687 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14393 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14394 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14395 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14396 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14397 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1688 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14402 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14403 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14405 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1689 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14411 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1690 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14419 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14421 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14423 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1691 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14429 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14430 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14433 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1692 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14438 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14441 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1693 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14447 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14449 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0369 Fin15AnchoredAtom0370 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1694 at hbad
  cases hcolor0 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14460 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14461 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
