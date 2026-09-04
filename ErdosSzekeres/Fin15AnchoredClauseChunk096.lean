module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 096. -/

theorem fin15Anchored_clause12288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0261 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1432 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12293 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12294 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0260 Fin15AnchoredAtom0262 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1433 at hbad
  cases hcolor0 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12302 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12303 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12304 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12305 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0261 Fin15AnchoredAtom0262 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1434 at hbad
  cases hcolor0 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12312 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0264 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1435 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0265 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1436 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12331 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0267 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1438 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12341 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12342 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12343 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0268 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1439 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12350 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12351 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12352 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12353 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0263 Fin15AnchoredAtom0269 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1440 at hbad
  cases hcolor0 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12359 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12361 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12362 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0265 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1441 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1442 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12370 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1442 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12371 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1442 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1442 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0266 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1442 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12376 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12377 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12378 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0267 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1443 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12384 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12387 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12388 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0268 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1444 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12395 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12396 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12397 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12399 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0264 Fin15AnchoredAtom0269 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1445 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12405 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12406 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12407 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12408 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0266 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1446 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12415 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
