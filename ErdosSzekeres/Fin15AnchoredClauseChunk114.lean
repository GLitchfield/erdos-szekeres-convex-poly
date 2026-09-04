module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 114. -/

theorem fin15Anchored_clause14592 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14593 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14594 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0378 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1709 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0376 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1710 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14612 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1711 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1711 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0377 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1711 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14615 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1712 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1712 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14617 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1712 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1712 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1712 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14620 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0375 Fin15AnchoredAtom0378 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1712 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14623 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0377 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1713 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14631 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14632 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0376 Fin15AnchoredAtom0378 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1714 at hbad
  cases hcolor0 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14640 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14641 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14642 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0377 Fin15AnchoredAtom0378 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1715 at hbad
  cases hcolor0 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14649 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14650 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14651 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0380 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1716 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14657 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14659 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14660 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0382 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1718 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14666 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14667 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14668 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14669 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14670 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14671 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0383 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1719 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14677 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14678 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14679 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0379 Fin15AnchoredAtom0384 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1720 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14686 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14687 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14689 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14690 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0382 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1722 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14696 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14697 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14698 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0383 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1723 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14704 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14706 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0380 Fin15AnchoredAtom0384 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1724 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1728 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14715 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1728 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14716 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1728 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14717 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1728 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1728 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0383 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1728 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
