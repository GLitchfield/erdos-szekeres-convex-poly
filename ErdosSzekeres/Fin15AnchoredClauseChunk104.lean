module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 104. -/

theorem fin15Anchored_clause13312 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0306 Fin15AnchoredAtom0307 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1554 at hbad
  cases hcolor0 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13319 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13320 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13321 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0309 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1555 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13329 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13330 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13331 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0310 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1556 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13341 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0312 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1558 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0313 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1559 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13355 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13356 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13358 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0308 Fin15AnchoredAtom0314 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1560 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13364 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13365 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13367 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0310 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1561 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1562 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1562 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1562 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13376 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1562 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1562 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1562 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0311 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1562 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13381 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13382 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0312 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1563 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13389 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13390 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13393 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0313 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1564 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13401 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13402 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13403 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13405 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13406 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0309 Fin15AnchoredAtom0314 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1565 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1566 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1566 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1566 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13415 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1566 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1566 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1566 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0311 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1566 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13419 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13421 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13423 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0312 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1567 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13429 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13430 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13433 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0310 Fin15AnchoredAtom0313 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1568 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
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

end ErdosSzekeres

end
