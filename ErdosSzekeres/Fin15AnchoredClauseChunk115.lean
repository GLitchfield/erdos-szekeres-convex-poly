module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 115. -/

theorem fin15Anchored_clause14720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
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

theorem fin15Anchored_clause14721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
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

theorem fin15Anchored_clause14722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
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

theorem fin15Anchored_clause14723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
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

theorem fin15Anchored_clause14724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
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

theorem fin15Anchored_clause14725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14727 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14728 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14729 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0382 Fin15AnchoredAtom0384 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1729 at hbad
  cases hcolor0 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14735 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14737 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14738 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14739 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0383 Fin15AnchoredAtom0384 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1730 at hbad
  cases hcolor0 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14747 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14751 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0386 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1731 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14758 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14759 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0387 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1732 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14767 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14769 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14770 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0388 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1733 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14778 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14779 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14780 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14781 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0385 Fin15AnchoredAtom0389 Fin15AnchoredAtom0393
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1734 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1735 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1735 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14790 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1735 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1735 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1735 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1735 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0387 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1735 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14795 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1736 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1736 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1736 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1736 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0388 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1736 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1737 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1737 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0386 Fin15AnchoredAtom0389 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1737 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14803 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14804 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14805 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0388 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1738 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14813 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14814 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14816 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14817 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14818 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0387 Fin15AnchoredAtom0389 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1739 at hbad
  cases hcolor0 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14824 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14825 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14826 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14827 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14828 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0388 Fin15AnchoredAtom0389 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1740 at hbad
  cases hcolor0 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14834 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14835 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14837 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14838 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0391 Fin15AnchoredAtom0394
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1741 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14844 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1742 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14845 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1742 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14846 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1742 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0392 Fin15AnchoredAtom0395
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1742 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
