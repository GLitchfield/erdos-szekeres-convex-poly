module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 119. -/

theorem fin15Anchored_clause15232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
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

theorem fin15Anchored_clause15233 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15234 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15235 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15236 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0428 Fin15AnchoredAtom0433
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1799 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15242 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15243 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15245 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15247 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0427 Fin15AnchoredAtom0429 Fin15AnchoredAtom0434
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1800 at hbad
  cases hcolor0 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15252 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0428 Fin15AnchoredAtom0429 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1801 at hbad
  cases hcolor0 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15262 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15263 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15266 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0433 Fin15AnchoredAtom0434 Fin15AnchoredAtom0435
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1805 at hbad
  cases hcolor0 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15273 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0437 Fin15AnchoredAtom0440
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1806 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1807 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15282 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1807 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1807 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1807 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1807 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0438 Fin15AnchoredAtom0441
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1807 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15287 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1808 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15288 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1808 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0436 Fin15AnchoredAtom0439 Fin15AnchoredAtom0442
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1808 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15293 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0438 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1809 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15299 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15300 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15302 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0437 Fin15AnchoredAtom0439 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1810 at hbad
  cases hcolor0 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15309 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15310 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15311 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15312 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0438 Fin15AnchoredAtom0439 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1811 at hbad
  cases hcolor0 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15319 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1812 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15320 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1812 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15321 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1812 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1812 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1812 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0441 Fin15AnchoredAtom0443
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1812 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1813 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15326 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1813 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15327 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1813 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1813 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1813 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0440 Fin15AnchoredAtom0442 Fin15AnchoredAtom0444
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1813 at hbad
  cases hcolor0 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15331 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1814 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1814 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0441 Fin15AnchoredAtom0442 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1814 at hbad
  cases hcolor0 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15335 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15336 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15337 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0443 Fin15AnchoredAtom0444 Fin15AnchoredAtom0445
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1815 at hbad
  cases hcolor0 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15345 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0447 Fin15AnchoredAtom0449
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1816 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1817 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15355 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1817 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15356 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1817 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1817 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15358 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1817 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0446 Fin15AnchoredAtom0448 Fin15AnchoredAtom0450
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1817 at hbad
  cases hcolor0 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
