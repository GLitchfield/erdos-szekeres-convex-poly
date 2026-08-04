module

public import ErdosSzekeres.IncomingStarTransition
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# A fixed-root incoming-star transition collision

This witness shows that child incoming-star spectra and every root-relevant
prefix do not algebraically determine the parent spectrum from the root split
law alone.  It is a negative control: the first coloring is not decomposable,
and both parents contain a strong six-set.
-/

namespace ErdosSzekeres
namespace IncomingStarTransitionCollision

open RankProfileCollision

def lower : Finset (Fin 9) := {5}

def upper : Finset (Fin 9) := Finset.univ.erase 5

/-- The root crossing law at the singleton lower child, with one exceptional
left triple inside the upper child. -/
def colorWithSpecial (a : Fin 9) : TripleColoring 9 := fun t ↦
  if t.i = 5 ∨ t.j = 5 ∨ t.k = 5 then
    if t.j = 5 then Turn.left else Turn.right
  else if t.i = a ∧ t.j = 7 ∧ t.k = 8 then Turn.left else Turn.right

def leftColor : TripleColoring 9 := colorWithSpecial 4

def rightColor : TripleColoring 9 := colorWithSpecial 6

def rightUpperTree : DecompositionTree 9 :=
  .node (.leaf 0)
    (.node (.leaf 1)
      (.node (.leaf 2)
        (.node (.leaf 3)
          (.node (.leaf 4)
            (.node (.leaf 7) (.node (.leaf 6) (.leaf 8))))))

def rightParentTree : DecompositionTree 9 :=
  .node (.leaf 5) rightUpperTree

def strongSix : Finset (Fin 9) := {0, 1, 2, 3, 4, 5}

theorem colorWithSpecial_root_split (a : Fin 9) :
    HasDeepBelowSplit (colorWithSpecial a) lower upper := by
  constructor
  · decide
  · rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [colorWithSpecial, lower, upper]

theorem left_root_split : HasDeepBelowSplit leftColor lower upper := by
  exact colorWithSpecial_root_split 4

theorem right_root_split : HasDeepBelowSplit rightColor lower upper := by
  exact colorWithSpecial_root_split 6

theorem complete_upper_pair_languages_equal :
    ∀ u v : Fin 9,
      TurnLanguage.pairTurnLanguage leftColor upper 4 u v =
        TurnLanguage.pairTurnLanguage rightColor upper 4 u v := by
  decide

theorem child_spectra_equal :
    (TurnLanguage.incomingStarSpectrum leftColor lower 4 =
        TurnLanguage.incomingStarSpectrum rightColor lower 4) ∧
      TurnLanguage.incomingStarSpectrum leftColor upper 4 =
        TurnLanguage.incomingStarSpectrum rightColor upper 4 := by
  decide

theorem root_prefix_equal :
    TurnLanguage.RootRelevantPrefixEq leftColor rightColor lower upper 4 := by
  constructor
  · intro cut _
    fin_cases cut <;> decide
  · intro cut _
    fin_cases cut <;> decide

theorem left_pair_seven_eight_has_lrr :
    [Turn.left, Turn.right, Turn.right] ∈
      TurnLanguage.pairTurnLanguage leftColor (lower ∪ upper) 4 7 8 := by
  decide

theorem right_pair_seven_eight_not_has_lrr :
    [Turn.left, Turn.right, Turn.right] ∉
      TurnLanguage.pairTurnLanguage rightColor (lower ∪ upper) 4 7 8 := by
  decide

theorem pair_seven_eight_ne :
    TurnLanguage.pairTurnLanguage leftColor (lower ∪ upper) 4 7 8 ≠
      TurnLanguage.pairTurnLanguage rightColor (lower ∪ upper) 4 7 8 := by
  intro h
  have := Finset.ext_iff.mp h [Turn.left, Turn.right, Turn.right]
  exact right_pair_seven_eight_not_has_lrr (this.mp left_pair_seven_eight_has_lrr)

theorem left_not_decomposable : ¬IsDecomposable leftColor := by
  intro h
  have hallowed := h.turnSequenceAllowed (i := 4) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  norm_num [leftColor, colorWithSpecial, TurnSequenceAllowed] at hallowed

theorem right_tree_coloring : rightParentTree.coloring = rightColor := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [rightParentTree, rightUpperTree, rightColor, colorWithSpecial,
      DecompositionTree.coloring, DecompositionTree.vertices]

theorem right_decomposable : IsDecomposable rightColor := by
  have hwell : rightParentTree.WellFormed := by
    simp [rightParentTree, rightUpperTree, DecompositionTree.WellFormed,
      DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn rightParentTree hwell
  have hvertices : rightParentTree.vertices = Finset.univ := by decide
  rw [hvertices, right_tree_coloring] at h
  exact h

theorem left_contains_strong_six :
    ContainsStrongPolygonSet leftColor Finset.univ 6 := by
  refine ⟨strongSix, by simp [strongSix], by decide, ?_⟩
  exact (strongPolygonSetBool_eq_true_iff leftColor strongSix).1 (by decide)

theorem right_contains_strong_six :
    ContainsStrongPolygonSet rightColor Finset.univ 6 := by
  refine ⟨strongSix, by simp [strongSix], by decide, ?_⟩
  exact (strongPolygonSetBool_eq_true_iff rightColor strongSix).1 (by decide)

theorem parent_spectra_ne :
    TurnLanguage.incomingStarSpectrum leftColor (lower ∪ upper) 4 ≠
      TurnLanguage.incomingStarSpectrum rightColor (lower ∪ upper) 4 := by
  decide

theorem fixed_root_transition_collision :
    HasDeepBelowSplit leftColor lower upper ∧
      HasDeepBelowSplit rightColor lower upper ∧
      TurnLanguage.incomingStarSpectrum leftColor lower 4 =
        TurnLanguage.incomingStarSpectrum rightColor lower 4 ∧
      TurnLanguage.incomingStarSpectrum leftColor upper 4 =
        TurnLanguage.incomingStarSpectrum rightColor upper 4 ∧
      TurnLanguage.RootRelevantPrefixEq leftColor rightColor lower upper 4 ∧
      TurnLanguage.incomingStarSpectrum leftColor (lower ∪ upper) 4 ≠
        TurnLanguage.incomingStarSpectrum rightColor (lower ∪ upper) 4 := by
  exact ⟨left_root_split, right_root_split, child_spectra_equal.1,
    child_spectra_equal.2, root_prefix_equal, parent_spectra_ne⟩

namespace DecomposableClosed

/-- A second collision has recursively decomposable colorings on both sides,
but both contain a strong six-set. -/
def leftUpperTree : DecompositionTree 9 :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.node (.node (.leaf 8) (.leaf 1)) (.leaf 2))
            (.leaf 3))
          (.leaf 4))
        (.leaf 0))
      (.leaf 6))
    (.leaf 7)

def rightUpperTree : DecompositionTree 9 :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.node (.node (.leaf 8) (.leaf 1)) (.leaf 2))
            (.leaf 3))
          (.leaf 4))
        (.leaf 6))
      (.leaf 0))
    (.leaf 7)

def leftTree : DecompositionTree 9 := .node (.leaf 5) leftUpperTree

def rightTree : DecompositionTree 9 := .node (.leaf 5) rightUpperTree

def leftColor : TripleColoring 9 := leftTree.coloring

def rightColor : TripleColoring 9 := rightTree.coloring

def strongSix : Finset (Fin 9) := {0, 1, 2, 3, 4, 6}

theorem left_decomposable : IsDecomposable leftColor := by
  have hwell : leftTree.WellFormed := by
    simp [leftTree, leftUpperTree, DecompositionTree.WellFormed,
      DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn leftTree hwell
  have hvertices : leftTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem right_decomposable : IsDecomposable rightColor := by
  have hwell : rightTree.WellFormed := by
    simp [rightTree, rightUpperTree, DecompositionTree.WellFormed,
      DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn rightTree hwell
  have hvertices : rightTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem left_root_split : HasDeepBelowSplit leftColor lower upper := by
  have h := DecompositionTree.node_split (.leaf 5) leftUpperTree (by
    simp [leftUpperTree, DecompositionTree.vertices])
  simpa [leftTree, leftColor, lower, upper, leftUpperTree,
    DecompositionTree.vertices] using h

theorem right_root_split : HasDeepBelowSplit rightColor lower upper := by
  have h := DecompositionTree.node_split (.leaf 5) rightUpperTree (by
    simp [rightUpperTree, DecompositionTree.vertices])
  simpa [rightTree, rightColor, lower, upper, rightUpperTree,
    DecompositionTree.vertices] using h

theorem child_spectra_equal :
    (TurnLanguage.incomingStarSpectrum leftColor lower 4 =
        TurnLanguage.incomingStarSpectrum rightColor lower 4) ∧
      TurnLanguage.incomingStarSpectrum leftColor upper 4 =
        TurnLanguage.incomingStarSpectrum rightColor upper 4 := by
  decide

theorem root_prefix_equal :
    TurnLanguage.RootRelevantPrefixEq leftColor rightColor lower upper 4 := by
  constructor
  · intro cut _
    fin_cases cut <;> decide
  · intro cut _
    fin_cases cut <;> decide

theorem parent_spectra_ne :
    TurnLanguage.incomingStarSpectrum leftColor Finset.univ 4 ≠
      TurnLanguage.incomingStarSpectrum rightColor Finset.univ 4 := by
  decide

theorem left_contains_strong_six :
    ContainsStrongPolygonSet leftColor Finset.univ 6 := by
  refine ⟨strongSix, by simp [strongSix], by decide, ?_⟩
  exact (strongPolygonSetBool_eq_true_iff leftColor strongSix).1 (by decide)

theorem right_contains_strong_six :
    ContainsStrongPolygonSet rightColor Finset.univ 6 := by
  refine ⟨strongSix, by simp [strongSix], by decide, ?_⟩
  exact (strongPolygonSetBool_eq_true_iff rightColor strongSix).1 (by decide)

theorem decomposable_closed_transition_collision :
    IsDecomposable leftColor ∧ IsDecomposable rightColor ∧
      HasDeepBelowSplit leftColor lower upper ∧
      HasDeepBelowSplit rightColor lower upper ∧
      TurnLanguage.incomingStarSpectrum leftColor lower 4 =
        TurnLanguage.incomingStarSpectrum rightColor lower 4 ∧
      TurnLanguage.incomingStarSpectrum leftColor upper 4 =
        TurnLanguage.incomingStarSpectrum rightColor upper 4 ∧
      TurnLanguage.RootRelevantPrefixEq leftColor rightColor lower upper 4 ∧
      TurnLanguage.incomingStarSpectrum leftColor Finset.univ 4 ≠
        TurnLanguage.incomingStarSpectrum rightColor Finset.univ 4 := by
  exact ⟨left_decomposable, right_decomposable, left_root_split,
    right_root_split, child_spectra_equal.1, child_spectra_equal.2,
    root_prefix_equal, parent_spectra_ne⟩

end DecomposableClosed

end IncomingStarTransitionCollision
end ErdosSzekeres

end
