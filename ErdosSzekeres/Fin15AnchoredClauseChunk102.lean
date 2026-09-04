module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 102. -/

theorem fin15Anchored_clause13056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1526 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1526 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1526 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0298 Fin15AnchoredAtom0299 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1526 at hbad
  cases hcolor0 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13060 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13062 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13063 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13064 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0301 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1527 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13071 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13072 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13073 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13074 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13075 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0302 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1528 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13080 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13081 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13082 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13083 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13084 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0303 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1529 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13089 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13090 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13093 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13094 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0304 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1530 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13103 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13106 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0305 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1531 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13111 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13115 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0306 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1532 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13122 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13123 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13126 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0300 Fin15AnchoredAtom0307 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1533 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13134 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13135 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0302 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1534 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13141 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13144 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13145 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0303 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1535 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13150 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0305 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1537 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13159 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0306 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1538 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13169 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0301 Fin15AnchoredAtom0307 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1539 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13179 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13181 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0302 Fin15AnchoredAtom0303 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1540 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
