module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 092. -/

theorem fin15Anchored_clause11776 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11783 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11784 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11785 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0244 Fin15AnchoredAtom0245 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1370 at hbad
  cases hcolor0 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11791 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11792 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11793 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11794 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1371 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11799 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11801 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11802 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11803 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1372 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11810 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11811 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11812 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11813 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11814 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1373 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11820 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11821 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11822 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11823 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1374 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11829 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1375 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1375 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1375 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11832 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1375 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1375 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1375 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1375 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11837 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11838 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1376 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11846 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11847 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1377 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11855 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11856 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11857 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11858 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11860 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1378 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11866 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11867 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11868 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11869 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11870 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1379 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11876 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11877 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11879 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1380 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11888 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11890 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1381 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1382 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1382 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1382 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11899 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11900 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11901 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11902 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11903 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
