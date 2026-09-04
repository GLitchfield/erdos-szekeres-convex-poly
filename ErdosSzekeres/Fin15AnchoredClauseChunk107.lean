module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 107. -/

theorem fin15Anchored_clause13696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13701 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13702 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0328 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1602 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13709 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13710 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13711 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13712 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0328 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1604 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13717 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13720 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13721 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13722 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0327 Fin15AnchoredAtom0329 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1605 at hbad
  cases hcolor0 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13728 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13729 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13732 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13733 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0328 Fin15AnchoredAtom0329 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1606 at hbad
  cases hcolor0 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13738 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13739 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0331 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1607 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0332 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1608 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0332 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1608 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0332 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1608 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13751 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0332 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1608 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0332 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1608 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0332 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1608 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0330 Fin15AnchoredAtom0332 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1608 at hbad
  cases hcolor0 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13758 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13759 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13760 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0333 Fin15AnchoredAtom0334 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1610 at hbad
  cases hcolor0 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13765 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13767 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13769 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0337 Fin15AnchoredAtom0344
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1611 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13775 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13776 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13778 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13779 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0338 Fin15AnchoredAtom0345
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1612 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13785 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13787 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13790 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0339 Fin15AnchoredAtom0346
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1613 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0340 Fin15AnchoredAtom0347
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1614 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0340 Fin15AnchoredAtom0347
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1614 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0340 Fin15AnchoredAtom0347
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1614 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0340 Fin15AnchoredAtom0347
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1614 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0340 Fin15AnchoredAtom0347
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1614 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13801 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13802 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13803 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13804 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13805 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0341 Fin15AnchoredAtom0348
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1615 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13812 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13813 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13814 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0342 Fin15AnchoredAtom0349
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1616 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13821 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13822 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13823 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
