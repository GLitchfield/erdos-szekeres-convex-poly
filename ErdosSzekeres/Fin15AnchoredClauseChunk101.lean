module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 101. -/

theorem fin15Anchored_clause12928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12929 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12930 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12931 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12937 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12938 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12939 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0295 Fin15AnchoredAtom0321
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1512 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12945 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12948 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0296 Fin15AnchoredAtom0322
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1513 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12954 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12957 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0297 Fin15AnchoredAtom0323
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1514 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12966 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12967 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12968 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0298 Fin15AnchoredAtom0324
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1515 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12979 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12980 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12981 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0294 Fin15AnchoredAtom0299 Fin15AnchoredAtom0325
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1516 at hbad
  cases hcolor0 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12986 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1517 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12987 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1517 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1517 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0296 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1517 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12990 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12991 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12992 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12993 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0297 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1518 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12998 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12999 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13003 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0298 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1519 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13008 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13009 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13010 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13011 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0295 Fin15AnchoredAtom0299 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1520 at hbad
  cases hcolor0 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13018 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1521 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1521 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13020 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1521 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1521 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1521 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0297 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1521 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13024 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1522 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1522 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0298 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1522 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13027 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom1523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0296 Fin15AnchoredAtom0299 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0368 Fin15AnchoredAtom1523 at hbad
  cases hcolor0 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13029 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13030 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13031 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13032 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13033 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0298 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1524 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13042 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13043 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13044 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0297 Fin15AnchoredAtom0299 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1525 at hbad
  cases hcolor0 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13050 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
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

theorem fin15Anchored_clause13051 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0298 chi ∧
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

theorem fin15Anchored_clause13052 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
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

theorem fin15Anchored_clause13053 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
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

theorem fin15Anchored_clause13054 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
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

theorem fin15Anchored_clause13055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
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

end ErdosSzekeres

end
