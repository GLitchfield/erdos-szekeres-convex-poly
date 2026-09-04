module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 072. -/

theorem fin15Anchored_clause09216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0128 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1001 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09221 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09222 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09223 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09224 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0129 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1002 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09232 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0131 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1004 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09239 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09240 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0132 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1005 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09245 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09247 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09248 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09249 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0127 Fin15AnchoredAtom0133 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1006 at hbad
  cases hcolor0 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09255 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09256 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09257 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0129 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1007 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1008 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1008 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1008 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1008 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0130 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1008 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09269 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09270 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09271 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0131 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1009 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09278 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0132 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1010 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09287 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09288 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09289 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0128 Fin15AnchoredAtom0133 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1011 at hbad
  cases hcolor0 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09298 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09299 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0130 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1012 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09305 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0131 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1013 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09316 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0132 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1014 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0129 Fin15AnchoredAtom0133 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1015 at hbad
  cases hcolor0 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09330 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1016 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1016 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1016 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1016 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1016 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1016 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1016 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1016 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1016 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0131 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1016 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09335 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1017 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0130 Fin15AnchoredAtom0132 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1017 at hbad
  cases hcolor0 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09336 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09337 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
