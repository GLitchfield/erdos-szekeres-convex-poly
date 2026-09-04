module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 108. -/

theorem fin15Anchored_clause13824 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13825 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13826 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0336 Fin15AnchoredAtom0343 Fin15AnchoredAtom0350
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1617 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13832 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13833 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13834 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13835 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0338 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1618 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13842 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13843 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13844 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1619 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13851 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13852 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13853 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1621 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13860 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13861 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13862 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13863 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1622 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13869 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13870 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13871 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1623 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13879 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1624 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1625 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13888 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1625 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1625 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13890 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1625 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1625 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1625 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1625 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13894 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13896 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13897 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13899 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 Fin15AnchoredAtom1626 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13904 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13906 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13907 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13908 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 Fin15AnchoredAtom1627 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13915 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13917 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13918 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13919 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 Fin15AnchoredAtom1628 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13925 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13927 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 Fin15AnchoredAtom1629 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13937 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13938 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13939 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 Fin15AnchoredAtom1630 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13945 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
