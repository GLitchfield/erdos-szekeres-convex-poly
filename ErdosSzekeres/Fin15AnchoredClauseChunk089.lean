module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 089. -/

theorem fin15Anchored_clause11392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11393 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11394 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11395 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11396 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0228 Fin15AnchoredAtom0229 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1321 at hbad
  cases hcolor0 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11403 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1322 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1322 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11405 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1322 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1322 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1322 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1322 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0231 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1322 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11410 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1323 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11411 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1323 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1323 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1323 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1323 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1323 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0230 Fin15AnchoredAtom0232 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1323 at hbad
  cases hcolor0 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11417 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1324 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1324 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11418 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1324 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1324 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1324 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0231 Fin15AnchoredAtom0232 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1324 at hbad
  cases hcolor0 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11421 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11423 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0233 Fin15AnchoredAtom0234 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1325 at hbad
  cases hcolor0 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11433 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11434 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0237 Fin15AnchoredAtom0246
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1326 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11441 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11443 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0238 Fin15AnchoredAtom0247
    Fin15AnchoredAtom0292 Fin15AnchoredAtom1327 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11449 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0239 Fin15AnchoredAtom0248
    Fin15AnchoredAtom0293 Fin15AnchoredAtom1328 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11460 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11461 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0240 Fin15AnchoredAtom0249
    Fin15AnchoredAtom0294 Fin15AnchoredAtom1329 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11467 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11469 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11470 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11471 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0241 Fin15AnchoredAtom0250
    Fin15AnchoredAtom0295 Fin15AnchoredAtom1330 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11477 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1331 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1331 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1331 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0242 Fin15AnchoredAtom0251
    Fin15AnchoredAtom0296 Fin15AnchoredAtom1331 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11481 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11482 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11483 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11485 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0243 Fin15AnchoredAtom0252
    Fin15AnchoredAtom0297 Fin15AnchoredAtom1332 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11491 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11492 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11493 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11494 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0244 Fin15AnchoredAtom0253
    Fin15AnchoredAtom0298 Fin15AnchoredAtom1333 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11502 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11503 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11504 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0236 Fin15AnchoredAtom0245 Fin15AnchoredAtom0254
    Fin15AnchoredAtom0299 Fin15AnchoredAtom1334 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11510 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11511 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0238 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0300 Fin15AnchoredAtom1335 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11518 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11519 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0239 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0301 Fin15AnchoredAtom1336 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
