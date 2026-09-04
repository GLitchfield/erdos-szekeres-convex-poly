module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 056. -/

theorem fin15Anchored_clause07168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0047 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0005 Fin15AnchoredAtom0047
    Fin15AnchoredAtom0125 Fin15AnchoredAtom0489 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07169 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0006 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0126 Fin15AnchoredAtom0490 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0048 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0006 Fin15AnchoredAtom0048
    Fin15AnchoredAtom0126 Fin15AnchoredAtom0490 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0007 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0127 Fin15AnchoredAtom0491 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0049 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0007 Fin15AnchoredAtom0049
    Fin15AnchoredAtom0127 Fin15AnchoredAtom0491 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07173 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0008 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0128 Fin15AnchoredAtom0492 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0050 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0008 Fin15AnchoredAtom0050
    Fin15AnchoredAtom0128 Fin15AnchoredAtom0492 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07175 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0009 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0129 Fin15AnchoredAtom0493 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07176 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0051 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0009 Fin15AnchoredAtom0051
    Fin15AnchoredAtom0129 Fin15AnchoredAtom0493 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07177 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0010 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0130 Fin15AnchoredAtom0494 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0052 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0010 Fin15AnchoredAtom0052
    Fin15AnchoredAtom0130 Fin15AnchoredAtom0494 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07179 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0011 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0131 Fin15AnchoredAtom0495 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0053 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0011 Fin15AnchoredAtom0053
    Fin15AnchoredAtom0131 Fin15AnchoredAtom0495 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07181 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0012 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0132 Fin15AnchoredAtom0496 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07182 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0054 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0012 Fin15AnchoredAtom0054
    Fin15AnchoredAtom0132 Fin15AnchoredAtom0496 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07183 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0013 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0133 Fin15AnchoredAtom0497 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0004 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0055 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0004 Fin15AnchoredAtom0013 Fin15AnchoredAtom0055
    Fin15AnchoredAtom0133 Fin15AnchoredAtom0497 at hbad
  cases hcolor0 : chi ⟨0, 1, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07185 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0006 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0134 Fin15AnchoredAtom0498 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07186 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0056 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0006 Fin15AnchoredAtom0056
    Fin15AnchoredAtom0134 Fin15AnchoredAtom0498 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07187 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0007 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0135 Fin15AnchoredAtom0499 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0057 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0007 Fin15AnchoredAtom0057
    Fin15AnchoredAtom0135 Fin15AnchoredAtom0499 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07189 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0008 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0136 Fin15AnchoredAtom0500 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0058 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0008 Fin15AnchoredAtom0058
    Fin15AnchoredAtom0136 Fin15AnchoredAtom0500 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0009 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0137 Fin15AnchoredAtom0501 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0059 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0009 Fin15AnchoredAtom0059
    Fin15AnchoredAtom0137 Fin15AnchoredAtom0501 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0010 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0138 Fin15AnchoredAtom0502 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07194 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0060 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0010 Fin15AnchoredAtom0060
    Fin15AnchoredAtom0138 Fin15AnchoredAtom0502 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07195 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0011 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0139 Fin15AnchoredAtom0503 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0061 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0011 Fin15AnchoredAtom0061
    Fin15AnchoredAtom0139 Fin15AnchoredAtom0503 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0012 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0140 Fin15AnchoredAtom0504 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07198 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0062 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0012 Fin15AnchoredAtom0062
    Fin15AnchoredAtom0140 Fin15AnchoredAtom0504 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0013 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0141 Fin15AnchoredAtom0505 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0005 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0063 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0005 Fin15AnchoredAtom0013 Fin15AnchoredAtom0063
    Fin15AnchoredAtom0141 Fin15AnchoredAtom0505 at hbad
  cases hcolor0 : chi ⟨0, 1, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07201 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0007 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0142 Fin15AnchoredAtom0506 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0064 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0007 Fin15AnchoredAtom0064
    Fin15AnchoredAtom0142 Fin15AnchoredAtom0506 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0008 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0143 Fin15AnchoredAtom0507 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07204 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0065 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0008 Fin15AnchoredAtom0065
    Fin15AnchoredAtom0143 Fin15AnchoredAtom0507 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07205 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0009 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0144 Fin15AnchoredAtom0508 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07206 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0066 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0009 Fin15AnchoredAtom0066
    Fin15AnchoredAtom0144 Fin15AnchoredAtom0508 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0010 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0145 Fin15AnchoredAtom0509 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0067 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0010 Fin15AnchoredAtom0067
    Fin15AnchoredAtom0145 Fin15AnchoredAtom0509 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0011 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0146 Fin15AnchoredAtom0510 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0068 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0011 Fin15AnchoredAtom0068
    Fin15AnchoredAtom0146 Fin15AnchoredAtom0510 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07211 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0012 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0147 Fin15AnchoredAtom0511 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07212 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0069 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0012 Fin15AnchoredAtom0069
    Fin15AnchoredAtom0147 Fin15AnchoredAtom0511 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07213 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0013 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0148 Fin15AnchoredAtom0512 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0006 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0070 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0006 Fin15AnchoredAtom0013 Fin15AnchoredAtom0070
    Fin15AnchoredAtom0148 Fin15AnchoredAtom0512 at hbad
  cases hcolor0 : chi ⟨0, 1, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07215 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0008 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0149 Fin15AnchoredAtom0513 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07216 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0071 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0008 Fin15AnchoredAtom0071
    Fin15AnchoredAtom0149 Fin15AnchoredAtom0513 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07217 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0009 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0150 Fin15AnchoredAtom0514 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07218 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0072 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0009 Fin15AnchoredAtom0072
    Fin15AnchoredAtom0150 Fin15AnchoredAtom0514 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0011 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0152 Fin15AnchoredAtom0516 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0074 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0011 Fin15AnchoredAtom0074
    Fin15AnchoredAtom0152 Fin15AnchoredAtom0516 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07221 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0012 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0153 Fin15AnchoredAtom0517 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07222 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0075 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0012 Fin15AnchoredAtom0075
    Fin15AnchoredAtom0153 Fin15AnchoredAtom0517 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07223 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0013 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0154 Fin15AnchoredAtom0518 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07224 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0007 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0076 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0007 Fin15AnchoredAtom0013 Fin15AnchoredAtom0076
    Fin15AnchoredAtom0154 Fin15AnchoredAtom0518 at hbad
  cases hcolor0 : chi ⟨0, 1, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07225 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0009 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0155 Fin15AnchoredAtom0519 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07226 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0077 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0009 Fin15AnchoredAtom0077
    Fin15AnchoredAtom0155 Fin15AnchoredAtom0519 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07227 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0010 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0156 Fin15AnchoredAtom0520 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0078 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0010 Fin15AnchoredAtom0078
    Fin15AnchoredAtom0156 Fin15AnchoredAtom0520 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0011 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0157 Fin15AnchoredAtom0521 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0079 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0011 Fin15AnchoredAtom0079
    Fin15AnchoredAtom0157 Fin15AnchoredAtom0521 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0012 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0158 Fin15AnchoredAtom0522 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07232 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0080 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0012 Fin15AnchoredAtom0080
    Fin15AnchoredAtom0158 Fin15AnchoredAtom0522 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07233 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0013 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0159 Fin15AnchoredAtom0523 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07234 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0008 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0081 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0008 Fin15AnchoredAtom0013 Fin15AnchoredAtom0081
    Fin15AnchoredAtom0159 Fin15AnchoredAtom0523 at hbad
  cases hcolor0 : chi ⟨0, 1, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07235 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0010 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0160 Fin15AnchoredAtom0524 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07236 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0082 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0010 Fin15AnchoredAtom0082
    Fin15AnchoredAtom0160 Fin15AnchoredAtom0524 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0011 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0161 Fin15AnchoredAtom0525 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0083 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0011 Fin15AnchoredAtom0083
    Fin15AnchoredAtom0161 Fin15AnchoredAtom0525 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07239 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0012 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0162 Fin15AnchoredAtom0526 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07240 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0084 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0012 Fin15AnchoredAtom0084
    Fin15AnchoredAtom0162 Fin15AnchoredAtom0526 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07241 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0013 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0163 Fin15AnchoredAtom0527 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07242 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0009 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0085 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0009 Fin15AnchoredAtom0013 Fin15AnchoredAtom0085
    Fin15AnchoredAtom0163 Fin15AnchoredAtom0527 at hbad
  cases hcolor0 : chi ⟨0, 1, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07243 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0010 Fin15AnchoredAtom0011 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0164 Fin15AnchoredAtom0528 at hbad
  cases hcolor0 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0086 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0010 Fin15AnchoredAtom0011 Fin15AnchoredAtom0086
    Fin15AnchoredAtom0164 Fin15AnchoredAtom0528 at hbad
  cases hcolor0 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07245 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0010 Fin15AnchoredAtom0012 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0165 Fin15AnchoredAtom0529 at hbad
  cases hcolor0 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0087 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0010 Fin15AnchoredAtom0012 Fin15AnchoredAtom0087
    Fin15AnchoredAtom0165 Fin15AnchoredAtom0529 at hbad
  cases hcolor0 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07247 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0010 Fin15AnchoredAtom0013 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0166 Fin15AnchoredAtom0530 at hbad
  cases hcolor0 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07248 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0010 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0088 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0010 Fin15AnchoredAtom0013 Fin15AnchoredAtom0088
    Fin15AnchoredAtom0166 Fin15AnchoredAtom0530 at hbad
  cases hcolor0 : chi ⟨0, 1, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07249 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0011 Fin15AnchoredAtom0012 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0167 Fin15AnchoredAtom0531 at hbad
  cases hcolor0 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0089 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0011 Fin15AnchoredAtom0012 Fin15AnchoredAtom0089
    Fin15AnchoredAtom0167 Fin15AnchoredAtom0531 at hbad
  cases hcolor0 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0011 Fin15AnchoredAtom0013 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0168 Fin15AnchoredAtom0532 at hbad
  cases hcolor0 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07252 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0011 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0090 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0011 Fin15AnchoredAtom0013 Fin15AnchoredAtom0090
    Fin15AnchoredAtom0168 Fin15AnchoredAtom0532 at hbad
  cases hcolor0 : chi ⟨0, 1, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0012 Fin15AnchoredAtom0013 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0169 Fin15AnchoredAtom0533 at hbad
  cases hcolor0 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0012 chi ∧
      ¬Fin15AnchoredAtom0013 chi ∧
      ¬Fin15AnchoredAtom0091 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0012 Fin15AnchoredAtom0013 Fin15AnchoredAtom0091
    Fin15AnchoredAtom0169 Fin15AnchoredAtom0533 at hbad
  cases hcolor0 : chi ⟨0, 1, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 1, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07255 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      ¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0015 Fin15AnchoredAtom0026
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0534 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07256 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0026 chi ∧
      Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0015 Fin15AnchoredAtom0026
    Fin15AnchoredAtom0170 Fin15AnchoredAtom0534 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 4, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07257 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0016 Fin15AnchoredAtom0027
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0535 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07258 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0027 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0016 Fin15AnchoredAtom0027
    Fin15AnchoredAtom0171 Fin15AnchoredAtom0535 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07259 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0017 Fin15AnchoredAtom0028
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0536 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07260 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0028 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0017 Fin15AnchoredAtom0028
    Fin15AnchoredAtom0172 Fin15AnchoredAtom0536 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0018 Fin15AnchoredAtom0029
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0537 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07262 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0029 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0018 Fin15AnchoredAtom0029
    Fin15AnchoredAtom0173 Fin15AnchoredAtom0537 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07263 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0019 Fin15AnchoredAtom0030
    Fin15AnchoredAtom0174 Fin15AnchoredAtom0538 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0030 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0019 Fin15AnchoredAtom0030
    Fin15AnchoredAtom0174 Fin15AnchoredAtom0538 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0020 Fin15AnchoredAtom0031
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0539 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07266 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0031 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0020 Fin15AnchoredAtom0031
    Fin15AnchoredAtom0175 Fin15AnchoredAtom0539 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07267 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0021 Fin15AnchoredAtom0032
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0540 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07268 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0032 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0021 Fin15AnchoredAtom0032
    Fin15AnchoredAtom0176 Fin15AnchoredAtom0540 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07269 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0022 Fin15AnchoredAtom0033
    Fin15AnchoredAtom0177 Fin15AnchoredAtom0541 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07270 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0033 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0022 Fin15AnchoredAtom0033
    Fin15AnchoredAtom0177 Fin15AnchoredAtom0541 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07271 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0023 Fin15AnchoredAtom0034
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0542 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0034 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0023 Fin15AnchoredAtom0034
    Fin15AnchoredAtom0178 Fin15AnchoredAtom0542 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07273 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0024 Fin15AnchoredAtom0035
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0543 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0035 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0024 Fin15AnchoredAtom0035
    Fin15AnchoredAtom0179 Fin15AnchoredAtom0543 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0025 Fin15AnchoredAtom0036
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0544 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0014 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0036 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0014 Fin15AnchoredAtom0025 Fin15AnchoredAtom0036
    Fin15AnchoredAtom0180 Fin15AnchoredAtom0544 at hbad
  cases hcolor0 : chi ⟨0, 2, 3, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 3, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07277 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0016 Fin15AnchoredAtom0037
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0545 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07278 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0016 chi ∧
      ¬Fin15AnchoredAtom0037 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0016 Fin15AnchoredAtom0037
    Fin15AnchoredAtom0181 Fin15AnchoredAtom0545 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0017 Fin15AnchoredAtom0038
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0546 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0017 chi ∧
      ¬Fin15AnchoredAtom0038 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0017 Fin15AnchoredAtom0038
    Fin15AnchoredAtom0182 Fin15AnchoredAtom0546 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0018 Fin15AnchoredAtom0039
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0547 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07282 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0018 chi ∧
      ¬Fin15AnchoredAtom0039 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0018 Fin15AnchoredAtom0039
    Fin15AnchoredAtom0183 Fin15AnchoredAtom0547 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0019 Fin15AnchoredAtom0040
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0548 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07284 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0019 chi ∧
      ¬Fin15AnchoredAtom0040 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0019 Fin15AnchoredAtom0040
    Fin15AnchoredAtom0184 Fin15AnchoredAtom0548 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0020 Fin15AnchoredAtom0041
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0549 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07286 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0020 chi ∧
      ¬Fin15AnchoredAtom0041 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0020 Fin15AnchoredAtom0041
    Fin15AnchoredAtom0185 Fin15AnchoredAtom0549 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07287 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0021 Fin15AnchoredAtom0042
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0550 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07288 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0021 chi ∧
      ¬Fin15AnchoredAtom0042 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0021 Fin15AnchoredAtom0042
    Fin15AnchoredAtom0186 Fin15AnchoredAtom0550 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07289 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0022 Fin15AnchoredAtom0043
    Fin15AnchoredAtom0187 Fin15AnchoredAtom0551 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0022 chi ∧
      ¬Fin15AnchoredAtom0043 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0022 Fin15AnchoredAtom0043
    Fin15AnchoredAtom0187 Fin15AnchoredAtom0551 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0023 Fin15AnchoredAtom0044
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0552 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0023 chi ∧
      ¬Fin15AnchoredAtom0044 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0023 Fin15AnchoredAtom0044
    Fin15AnchoredAtom0188 Fin15AnchoredAtom0552 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07293 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0024 Fin15AnchoredAtom0045
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0553 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07294 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0024 chi ∧
      ¬Fin15AnchoredAtom0045 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0024 Fin15AnchoredAtom0045
    Fin15AnchoredAtom0189 Fin15AnchoredAtom0553 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause07295 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0015 chi ∧
      ¬Fin15AnchoredAtom0025 chi ∧
      ¬Fin15AnchoredAtom0046 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0015 Fin15AnchoredAtom0025 Fin15AnchoredAtom0046
    Fin15AnchoredAtom0190 Fin15AnchoredAtom0554 at hbad
  cases hcolor0 : chi ⟨0, 2, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
