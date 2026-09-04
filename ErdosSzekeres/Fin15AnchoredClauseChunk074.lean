module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 074. -/

theorem fin15Anchored_clause09472 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09479 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1036 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09480 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1036 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09481 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1036 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1036 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0138 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1036 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09485 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09488 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0139 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1037 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09494 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09496 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09497 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09498 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0140 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1038 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09504 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09506 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09507 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09508 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0141 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1039 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09515 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1040 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09516 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1040 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09517 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1040 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09518 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1040 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0138 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1040 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09520 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09521 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09522 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0139 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1041 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09531 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09532 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0140 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1042 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09538 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0137 Fin15AnchoredAtom0141 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1043 at hbad
  cases hcolor0 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09546 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0139 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1044 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09547 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0139 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1044 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0139 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1044 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0139 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1044 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0139 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1044 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0139 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1044 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom1046 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0141 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1046 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1046 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0138 Fin15AnchoredAtom0141 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1046 at hbad
  cases hcolor0 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09554 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09555 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09556 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0140 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1047 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09567 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09568 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0139 Fin15AnchoredAtom0141 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1048 at hbad
  cases hcolor0 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09576 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09577 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0140 Fin15AnchoredAtom0141 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1049 at hbad
  cases hcolor0 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09585 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09588 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0143 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1050 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09594 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
