module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 116. -/

theorem fin15Anchored_clause14848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
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

theorem fin15Anchored_clause14849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1743 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1743 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14851 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0390 Fin15AnchoredAtom0393 Fin15AnchoredAtom0396
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1743 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14852 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14853 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14854 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14855 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14856 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14857 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14858 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0392 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1744 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14864 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14866 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14867 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0391 Fin15AnchoredAtom0393 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1745 at hbad
  cases hcolor0 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14873 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14874 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14875 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14876 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14877 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0392 Fin15AnchoredAtom0393 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1746 at hbad
  cases hcolor0 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14882 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1747 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1747 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1747 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1747 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0395 Fin15AnchoredAtom0397
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1747 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1748 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14888 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1748 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1748 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1748 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0394 Fin15AnchoredAtom0396 Fin15AnchoredAtom0398
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1748 at hbad
  cases hcolor0 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14892 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14894 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14896 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14897 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0397 Fin15AnchoredAtom0398 Fin15AnchoredAtom0399
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1750 at hbad
  cases hcolor0 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14904 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14906 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14907 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14908 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0401 Fin15AnchoredAtom0406
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1751 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14914 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14915 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14917 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14918 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14919 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0403 Fin15AnchoredAtom0408
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1753 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14925 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14927 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14929 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14930 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0404 Fin15AnchoredAtom0409
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1754 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14937 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14938 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0400 Fin15AnchoredAtom0405 Fin15AnchoredAtom0410
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1755 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14945 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14948 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0403 Fin15AnchoredAtom0412
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1757 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14957 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14960 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0404 Fin15AnchoredAtom0413
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1758 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14966 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14967 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14968 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0401 Fin15AnchoredAtom0405 Fin15AnchoredAtom0414
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1759 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
