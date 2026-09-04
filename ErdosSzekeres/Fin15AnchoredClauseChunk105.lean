module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 105. -/

theorem fin15Anchored_clause13440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13441 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0314 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1569 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13449 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0312 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1570 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0313 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1571 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0313 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1571 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1572 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1572 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1572 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1572 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1572 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0311 Fin15AnchoredAtom0314 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1572 at hbad
  cases hcolor0 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13464 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13465 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13466 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13467 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0313 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1573 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13473 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13474 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13475 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13476 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13477 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0312 Fin15AnchoredAtom0314 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1574 at hbad
  cases hcolor0 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13483 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13485 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13488 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0313 Fin15AnchoredAtom0314 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1575 at hbad
  cases hcolor0 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13496 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13497 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13498 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13499 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13500 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0316 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1576 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13508 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13510 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13511 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0318 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1578 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13518 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13519 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13520 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13521 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13522 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0319 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1579 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13531 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13532 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13534 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13536 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0315 Fin15AnchoredAtom0320 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1580 at hbad
  cases hcolor0 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13542 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13543 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13544 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13545 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13546 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0318 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1582 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13553 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13554 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13555 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13556 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0319 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1583 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13563 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13564 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13567 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
