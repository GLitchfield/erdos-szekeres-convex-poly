module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 118. -/

theorem fin15Anchored_clause15104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0413 Fin15AnchoredAtom0416
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1777 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15107 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0414 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1778 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15108 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0414 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1778 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15109 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0414 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1778 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0414 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1778 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0414 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1778 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0414 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1778 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0411 Fin15AnchoredAtom0414 Fin15AnchoredAtom0417
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1778 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15115 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15116 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15117 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15118 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0413 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1779 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15126 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15127 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15128 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0412 Fin15AnchoredAtom0414 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1780 at hbad
  cases hcolor0 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15134 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15135 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15138 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0413 Fin15AnchoredAtom0414 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1781 at hbad
  cases hcolor0 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15144 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15145 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15146 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15147 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15148 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0416 Fin15AnchoredAtom0418
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1782 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15156 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0415 Fin15AnchoredAtom0417 Fin15AnchoredAtom0419
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1783 at hbad
  cases hcolor0 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0416 Fin15AnchoredAtom0417 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1784 at hbad
  cases hcolor0 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0416 Fin15AnchoredAtom0417 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1784 at hbad
  cases hcolor0 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0416 Fin15AnchoredAtom0417 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1784 at hbad
  cases hcolor0 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0416 Fin15AnchoredAtom0417 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1784 at hbad
  cases hcolor0 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15167 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15169 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0418 Fin15AnchoredAtom0419 Fin15AnchoredAtom0420
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1785 at hbad
  cases hcolor0 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15177 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15179 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0423 Fin15AnchoredAtom0427
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1787 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15189 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0424 Fin15AnchoredAtom0428
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1788 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15198 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0421 Fin15AnchoredAtom0425 Fin15AnchoredAtom0429
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1789 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15205 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15206 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0424 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1793 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15216 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15217 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15218 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0423 Fin15AnchoredAtom0425 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1794 at hbad
  cases hcolor0 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15224 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15225 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15226 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15227 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0424 Fin15AnchoredAtom0425 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1795 at hbad
  cases hcolor0 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
