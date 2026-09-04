module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 059. -/

theorem fin15Anchored_clause07552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0043 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0686 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07553 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0043 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0686 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07554 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0044 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0687 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07555 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0044 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0687 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07556 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0045 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0688 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0045 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0688 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0046 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0689 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07559 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 Fin15AnchoredAtom0046 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0689 at hbad
  cases hcolor0 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07560 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0043 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0326 Fin15AnchoredAtom0690 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07561 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0043 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0326 Fin15AnchoredAtom0690 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07562 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0044 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0691 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07563 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0044 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0691 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07564 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0045 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0692 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0045 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0692 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0046 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0693 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07567 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 Fin15AnchoredAtom0046 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0693 at hbad
  cases hcolor0 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07568 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0043 Fin15AnchoredAtom0044 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0694 at hbad
  cases hcolor0 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0043 Fin15AnchoredAtom0044 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0694 at hbad
  cases hcolor0 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07570 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0043 Fin15AnchoredAtom0045 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0331 Fin15AnchoredAtom0695 at hbad
  cases hcolor0 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07571 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0043 Fin15AnchoredAtom0045 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0331 Fin15AnchoredAtom0695 at hbad
  cases hcolor0 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07572 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0043 Fin15AnchoredAtom0046 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0332 Fin15AnchoredAtom0696 at hbad
  cases hcolor0 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07573 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0043 Fin15AnchoredAtom0046 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0332 Fin15AnchoredAtom0696 at hbad
  cases hcolor0 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0044 Fin15AnchoredAtom0045 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0697 at hbad
  cases hcolor0 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0044 Fin15AnchoredAtom0045 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0697 at hbad
  cases hcolor0 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07576 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0044 Fin15AnchoredAtom0046 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0698 at hbad
  cases hcolor0 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07577 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0044 Fin15AnchoredAtom0046 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0698 at hbad
  cases hcolor0 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0045 Fin15AnchoredAtom0046 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0699 at hbad
  cases hcolor0 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07579 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0045 Fin15AnchoredAtom0046 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0699 at hbad
  cases hcolor0 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07580 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0048 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0700 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07581 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0048 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0700 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07582 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0049 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0701 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07583 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0049 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0701 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0050 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0702 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07585 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0050 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0338 Fin15AnchoredAtom0702 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0051 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0703 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0051 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0339 Fin15AnchoredAtom0703 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07588 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0052 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0704 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07589 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0052 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0340 Fin15AnchoredAtom0704 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07590 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0053 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0705 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07591 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0053 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0341 Fin15AnchoredAtom0705 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07592 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0054 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0706 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07593 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0054 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0342 Fin15AnchoredAtom0706 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07594 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0055 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0707 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0047 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 Fin15AnchoredAtom0055 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0343 Fin15AnchoredAtom0707 at hbad
  cases hcolor0 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0049 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0708 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0049 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0344 Fin15AnchoredAtom0708 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0050 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0709 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0050 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0345 Fin15AnchoredAtom0709 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07600 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0051 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0710 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07601 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0051 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0346 Fin15AnchoredAtom0710 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07602 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0052 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0347 Fin15AnchoredAtom0711 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07603 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0052 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0347 Fin15AnchoredAtom0711 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0053 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0712 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0053 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0348 Fin15AnchoredAtom0712 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0054 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0713 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0054 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0349 Fin15AnchoredAtom0713 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0055 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0350 Fin15AnchoredAtom0714 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07609 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 Fin15AnchoredAtom0055 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0350 Fin15AnchoredAtom0714 at hbad
  cases hcolor0 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07610 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0050 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0351 Fin15AnchoredAtom0715 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07611 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0050 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0351 Fin15AnchoredAtom0715 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07612 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0051 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0352 Fin15AnchoredAtom0716 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0051 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0352 Fin15AnchoredAtom0716 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07614 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0053 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0354 Fin15AnchoredAtom0718 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07615 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0053 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0354 Fin15AnchoredAtom0718 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0054 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0355 Fin15AnchoredAtom0719 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07617 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0054 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0355 Fin15AnchoredAtom0719 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0055 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0356 Fin15AnchoredAtom0720 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 Fin15AnchoredAtom0055 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0356 Fin15AnchoredAtom0720 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07620 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0051 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0357 Fin15AnchoredAtom0721 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0051 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0357 Fin15AnchoredAtom0721 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0052 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0358 Fin15AnchoredAtom0722 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07623 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0052 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0358 Fin15AnchoredAtom0722 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0053 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0359 Fin15AnchoredAtom0723 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07625 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0053 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0359 Fin15AnchoredAtom0723 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07626 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0054 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0360 Fin15AnchoredAtom0724 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07627 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0054 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0360 Fin15AnchoredAtom0724 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0055 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0361 Fin15AnchoredAtom0725 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07629 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 Fin15AnchoredAtom0055 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0361 Fin15AnchoredAtom0725 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0052 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0362 Fin15AnchoredAtom0726 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07631 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0052 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0362 Fin15AnchoredAtom0726 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07632 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0053 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0363 Fin15AnchoredAtom0727 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0053 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0363 Fin15AnchoredAtom0727 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07634 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0054 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0364 Fin15AnchoredAtom0728 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07635 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0054 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0364 Fin15AnchoredAtom0728 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07636 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0055 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0365 Fin15AnchoredAtom0729 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 Fin15AnchoredAtom0055 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0365 Fin15AnchoredAtom0729 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0052 Fin15AnchoredAtom0053 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0366 Fin15AnchoredAtom0730 at hbad
  cases hcolor0 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0052 Fin15AnchoredAtom0053 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0366 Fin15AnchoredAtom0730 at hbad
  cases hcolor0 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07640 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0052 Fin15AnchoredAtom0054 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0367 Fin15AnchoredAtom0731 at hbad
  cases hcolor0 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07641 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0052 Fin15AnchoredAtom0054 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0367 Fin15AnchoredAtom0731 at hbad
  cases hcolor0 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07642 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0052 Fin15AnchoredAtom0055 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0368 Fin15AnchoredAtom0732 at hbad
  cases hcolor0 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07643 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0052 Fin15AnchoredAtom0055 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0368 Fin15AnchoredAtom0732 at hbad
  cases hcolor0 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0053 Fin15AnchoredAtom0054 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0369 Fin15AnchoredAtom0733 at hbad
  cases hcolor0 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0053 Fin15AnchoredAtom0054 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0369 Fin15AnchoredAtom0733 at hbad
  cases hcolor0 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0053 Fin15AnchoredAtom0055 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0370 Fin15AnchoredAtom0734 at hbad
  cases hcolor0 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07647 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0053 Fin15AnchoredAtom0055 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0370 Fin15AnchoredAtom0734 at hbad
  cases hcolor0 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0054 Fin15AnchoredAtom0055 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0371 Fin15AnchoredAtom0735 at hbad
  cases hcolor0 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07649 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0054 Fin15AnchoredAtom0055 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0371 Fin15AnchoredAtom0735 at hbad
  cases hcolor0 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07650 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0057 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0372 Fin15AnchoredAtom0736 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07651 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0057 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0372 Fin15AnchoredAtom0736 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07652 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0058 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0373 Fin15AnchoredAtom0737 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07653 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0058 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0373 Fin15AnchoredAtom0737 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0059 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0374 Fin15AnchoredAtom0738 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07655 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0059 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0374 Fin15AnchoredAtom0738 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0060 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0375 Fin15AnchoredAtom0739 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07657 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0060 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0375 Fin15AnchoredAtom0739 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0061 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0376 Fin15AnchoredAtom0740 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07659 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0061 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0376 Fin15AnchoredAtom0740 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07660 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0062 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0377 Fin15AnchoredAtom0741 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07661 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0062 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0377 Fin15AnchoredAtom0741 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07662 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0063 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0378 Fin15AnchoredAtom0742 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07663 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 Fin15AnchoredAtom0063 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0378 Fin15AnchoredAtom0742 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0058 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0379 Fin15AnchoredAtom0743 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0058 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0379 Fin15AnchoredAtom0743 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07666 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0059 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0380 Fin15AnchoredAtom0744 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07667 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0059 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0380 Fin15AnchoredAtom0744 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07668 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0061 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0382 Fin15AnchoredAtom0746 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07669 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0061 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0382 Fin15AnchoredAtom0746 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07670 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0062 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0383 Fin15AnchoredAtom0747 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07671 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0062 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0383 Fin15AnchoredAtom0747 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07672 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0063 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0384 Fin15AnchoredAtom0748 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07673 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 Fin15AnchoredAtom0063 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0384 Fin15AnchoredAtom0748 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07674 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0059 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0385 Fin15AnchoredAtom0749 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07675 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0059 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0385 Fin15AnchoredAtom0749 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0060 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0386 Fin15AnchoredAtom0750 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07677 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0060 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0386 Fin15AnchoredAtom0750 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07678 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0061 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0387 Fin15AnchoredAtom0751 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07679 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 Fin15AnchoredAtom0061 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0387 Fin15AnchoredAtom0751 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
