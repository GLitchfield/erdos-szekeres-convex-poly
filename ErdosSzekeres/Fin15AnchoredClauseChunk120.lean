module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 120. -/

theorem fin15Anchored_clause15360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
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

theorem fin15Anchored_clause15361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
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

theorem fin15Anchored_clause15362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0448 chi ∧
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

theorem fin15Anchored_clause15363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1818 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15364 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1818 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1818 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1818 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1818 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1818 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0447 Fin15AnchoredAtom0448 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1818 at hbad
  cases hcolor0 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15370 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15371 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0449 Fin15AnchoredAtom0450 Fin15AnchoredAtom0451
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1819 at hbad
  cases hcolor0 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15379 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1820 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1820 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0452 Fin15AnchoredAtom0453 Fin15AnchoredAtom0454
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1820 at hbad
  cases hcolor0 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause15382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00031
  ] at hbad
  tauto

theorem fin15Anchored_clause15383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00031
  ] at hbad
  tauto

theorem fin15Anchored_clause15384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00031
  ] at hbad
  tauto

theorem fin15Anchored_clause15385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom1821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00031
  ] at hbad
  tauto

theorem fin15Anchored_clause15386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom1821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00031
  ] at hbad
  tauto

theorem fin15Anchored_clause15387 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0457 Fin15AnchoredAtom0468
    Fin15AnchoredAtom0534 Fin15AnchoredAtom0820 Fin15AnchoredAtom1821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00031
  ] at hbad
  tauto

theorem fin15Anchored_clause15388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00047
  ] at hbad
  tauto

theorem fin15Anchored_clause15389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00047
  ] at hbad
  tauto

theorem fin15Anchored_clause15390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00047
  ] at hbad
  tauto

theorem fin15Anchored_clause15391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom1822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00047
  ] at hbad
  tauto

theorem fin15Anchored_clause15392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom1822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00047
  ] at hbad
  tauto

theorem fin15Anchored_clause15393 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0458 Fin15AnchoredAtom0469
    Fin15AnchoredAtom0535 Fin15AnchoredAtom0821 Fin15AnchoredAtom1822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00047
  ] at hbad
  tauto

theorem fin15Anchored_clause15394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00079
  ] at hbad
  tauto

theorem fin15Anchored_clause15395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00079
  ] at hbad
  tauto

theorem fin15Anchored_clause15396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00079
  ] at hbad
  tauto

theorem fin15Anchored_clause15397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom1823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00079
  ] at hbad
  tauto

theorem fin15Anchored_clause15398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom1823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00079
  ] at hbad
  tauto

theorem fin15Anchored_clause15399 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0459 Fin15AnchoredAtom0470
    Fin15AnchoredAtom0536 Fin15AnchoredAtom0822 Fin15AnchoredAtom1823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00079
  ] at hbad
  tauto

theorem fin15Anchored_clause15400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00143
  ] at hbad
  tauto

theorem fin15Anchored_clause15401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00143
  ] at hbad
  tauto

theorem fin15Anchored_clause15402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00143
  ] at hbad
  tauto

theorem fin15Anchored_clause15403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom1824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00143
  ] at hbad
  tauto

theorem fin15Anchored_clause15404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom1824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00143
  ] at hbad
  tauto

theorem fin15Anchored_clause15405 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0460 Fin15AnchoredAtom0471
    Fin15AnchoredAtom0537 Fin15AnchoredAtom0823 Fin15AnchoredAtom1824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00143
  ] at hbad
  tauto

theorem fin15Anchored_clause15406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00271
  ] at hbad
  tauto

theorem fin15Anchored_clause15407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom1825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00271
  ] at hbad
  tauto

theorem fin15Anchored_clause15408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00271
  ] at hbad
  tauto

theorem fin15Anchored_clause15409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom1825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00271
  ] at hbad
  tauto

theorem fin15Anchored_clause15410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1825 chi ∧
      ¬Fin15AnchoredAtom0824 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0824 Fin15AnchoredAtom1825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00271
  ] at hbad
  tauto

theorem fin15Anchored_clause15411 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0824 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0461 Fin15AnchoredAtom0472
    Fin15AnchoredAtom0538 Fin15AnchoredAtom0824 Fin15AnchoredAtom1825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00271
  ] at hbad
  tauto

theorem fin15Anchored_clause15412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00527
  ] at hbad
  tauto

theorem fin15Anchored_clause15413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00527
  ] at hbad
  tauto

theorem fin15Anchored_clause15414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00527
  ] at hbad
  tauto

theorem fin15Anchored_clause15415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom1826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00527
  ] at hbad
  tauto

theorem fin15Anchored_clause15416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom1826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00527
  ] at hbad
  tauto

theorem fin15Anchored_clause15417 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0462 Fin15AnchoredAtom0473
    Fin15AnchoredAtom0539 Fin15AnchoredAtom0825 Fin15AnchoredAtom1826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00527
  ] at hbad
  tauto

theorem fin15Anchored_clause15418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01039
  ] at hbad
  tauto

theorem fin15Anchored_clause15419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01039
  ] at hbad
  tauto

theorem fin15Anchored_clause15420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01039
  ] at hbad
  tauto

theorem fin15Anchored_clause15421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom1827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01039
  ] at hbad
  tauto

theorem fin15Anchored_clause15422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom1827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01039
  ] at hbad
  tauto

theorem fin15Anchored_clause15423 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0463 Fin15AnchoredAtom0474
    Fin15AnchoredAtom0540 Fin15AnchoredAtom0826 Fin15AnchoredAtom1827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01039
  ] at hbad
  tauto

theorem fin15Anchored_clause15424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02063
  ] at hbad
  tauto

theorem fin15Anchored_clause15425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0464 Fin15AnchoredAtom1828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02063
  ] at hbad
  tauto

theorem fin15Anchored_clause15426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom1828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02063
  ] at hbad
  tauto

theorem fin15Anchored_clause15427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom1828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02063
  ] at hbad
  tauto

theorem fin15Anchored_clause15428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1828 chi ∧
      ¬Fin15AnchoredAtom0827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0827 Fin15AnchoredAtom1828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02063
  ] at hbad
  tauto

theorem fin15Anchored_clause15429 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0464 Fin15AnchoredAtom0475
    Fin15AnchoredAtom0541 Fin15AnchoredAtom0827 Fin15AnchoredAtom1828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02063
  ] at hbad
  tauto

theorem fin15Anchored_clause15430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04111
  ] at hbad
  tauto

theorem fin15Anchored_clause15431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04111
  ] at hbad
  tauto

theorem fin15Anchored_clause15432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04111
  ] at hbad
  tauto

theorem fin15Anchored_clause15433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom1829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04111
  ] at hbad
  tauto

theorem fin15Anchored_clause15434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom1829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04111
  ] at hbad
  tauto

theorem fin15Anchored_clause15435 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0465 Fin15AnchoredAtom0476
    Fin15AnchoredAtom0542 Fin15AnchoredAtom0828 Fin15AnchoredAtom1829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04111
  ] at hbad
  tauto

theorem fin15Anchored_clause15436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08207
  ] at hbad
  tauto

theorem fin15Anchored_clause15437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08207
  ] at hbad
  tauto

theorem fin15Anchored_clause15438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08207
  ] at hbad
  tauto

theorem fin15Anchored_clause15439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom1830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08207
  ] at hbad
  tauto

theorem fin15Anchored_clause15440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom1830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08207
  ] at hbad
  tauto

theorem fin15Anchored_clause15441 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0466 Fin15AnchoredAtom0477
    Fin15AnchoredAtom0543 Fin15AnchoredAtom0829 Fin15AnchoredAtom1830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08207
  ] at hbad
  tauto

theorem fin15Anchored_clause15442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom1831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16399
  ] at hbad
  tauto

theorem fin15Anchored_clause15443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16399
  ] at hbad
  tauto

theorem fin15Anchored_clause15444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16399
  ] at hbad
  tauto

theorem fin15Anchored_clause15445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom1831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16399
  ] at hbad
  tauto

theorem fin15Anchored_clause15446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom1831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16399
  ] at hbad
  tauto

theorem fin15Anchored_clause15447 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom0456 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0456 Fin15AnchoredAtom0467 Fin15AnchoredAtom0478
    Fin15AnchoredAtom0544 Fin15AnchoredAtom0830 Fin15AnchoredAtom1831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16399
  ] at hbad
  tauto

theorem fin15Anchored_clause15448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00055
  ] at hbad
  tauto

theorem fin15Anchored_clause15449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00055
  ] at hbad
  tauto

theorem fin15Anchored_clause15450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00055
  ] at hbad
  tauto

theorem fin15Anchored_clause15451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom1832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00055
  ] at hbad
  tauto

theorem fin15Anchored_clause15452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom1832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00055
  ] at hbad
  tauto

theorem fin15Anchored_clause15453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0458 Fin15AnchoredAtom0479
    Fin15AnchoredAtom0545 Fin15AnchoredAtom0831 Fin15AnchoredAtom1832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00055
  ] at hbad
  tauto

theorem fin15Anchored_clause15454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00087
  ] at hbad
  tauto

theorem fin15Anchored_clause15455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00087
  ] at hbad
  tauto

theorem fin15Anchored_clause15456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00087
  ] at hbad
  tauto

theorem fin15Anchored_clause15457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom1833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00087
  ] at hbad
  tauto

theorem fin15Anchored_clause15458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom1833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00087
  ] at hbad
  tauto

theorem fin15Anchored_clause15459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0459 Fin15AnchoredAtom0480
    Fin15AnchoredAtom0546 Fin15AnchoredAtom0832 Fin15AnchoredAtom1833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00087
  ] at hbad
  tauto

theorem fin15Anchored_clause15460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00151
  ] at hbad
  tauto

theorem fin15Anchored_clause15461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00151
  ] at hbad
  tauto

theorem fin15Anchored_clause15462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00151
  ] at hbad
  tauto

theorem fin15Anchored_clause15463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom1834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00151
  ] at hbad
  tauto

theorem fin15Anchored_clause15464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom1834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00151
  ] at hbad
  tauto

theorem fin15Anchored_clause15465 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0460 Fin15AnchoredAtom0481
    Fin15AnchoredAtom0547 Fin15AnchoredAtom0833 Fin15AnchoredAtom1834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00151
  ] at hbad
  tauto

theorem fin15Anchored_clause15466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00279
  ] at hbad
  tauto

theorem fin15Anchored_clause15467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom1835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00279
  ] at hbad
  tauto

theorem fin15Anchored_clause15468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00279
  ] at hbad
  tauto

theorem fin15Anchored_clause15469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0548 Fin15AnchoredAtom1835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00279
  ] at hbad
  tauto

theorem fin15Anchored_clause15470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1835 chi ∧
      ¬Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0834 Fin15AnchoredAtom1835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00279
  ] at hbad
  tauto

theorem fin15Anchored_clause15471 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1835 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0834 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0461 Fin15AnchoredAtom0482
    Fin15AnchoredAtom0548 Fin15AnchoredAtom0834 Fin15AnchoredAtom1835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00279
  ] at hbad
  tauto

theorem fin15Anchored_clause15472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00535
  ] at hbad
  tauto

theorem fin15Anchored_clause15473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00535
  ] at hbad
  tauto

theorem fin15Anchored_clause15474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00535
  ] at hbad
  tauto

theorem fin15Anchored_clause15475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom1836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00535
  ] at hbad
  tauto

theorem fin15Anchored_clause15476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom1836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00535
  ] at hbad
  tauto

theorem fin15Anchored_clause15477 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0462 Fin15AnchoredAtom0483
    Fin15AnchoredAtom0549 Fin15AnchoredAtom0835 Fin15AnchoredAtom1836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00535
  ] at hbad
  tauto

theorem fin15Anchored_clause15478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01047
  ] at hbad
  tauto

theorem fin15Anchored_clause15479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01047
  ] at hbad
  tauto

theorem fin15Anchored_clause15480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01047
  ] at hbad
  tauto

theorem fin15Anchored_clause15481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom1837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01047
  ] at hbad
  tauto

theorem fin15Anchored_clause15482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom1837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01047
  ] at hbad
  tauto

theorem fin15Anchored_clause15483 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0463 Fin15AnchoredAtom0484
    Fin15AnchoredAtom0550 Fin15AnchoredAtom0836 Fin15AnchoredAtom1837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01047
  ] at hbad
  tauto

theorem fin15Anchored_clause15484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02071
  ] at hbad
  tauto

theorem fin15Anchored_clause15485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom0551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0551 Fin15AnchoredAtom1838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02071
  ] at hbad
  tauto

theorem fin15Anchored_clause15486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1838 chi ∧
      ¬Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0837 Fin15AnchoredAtom1838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02071
  ] at hbad
  tauto

theorem fin15Anchored_clause15487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1838 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0464 Fin15AnchoredAtom0485
    Fin15AnchoredAtom0551 Fin15AnchoredAtom0837 Fin15AnchoredAtom1838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02071
  ] at hbad
  tauto

end ErdosSzekeres

end
