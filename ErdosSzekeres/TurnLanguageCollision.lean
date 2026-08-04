module

public import ErdosSzekeres.RankProfileCollision
public import ErdosSzekeres.TurnLanguage

@[expose] public section

/-!
# An open collision for the endpoint-forgetting pair-language spectrum

This file kernel-checks the smallest collision found after the proposed
turn-language spectrum was tested at its required depth.  The two lower
children have equal spectra through depth four, but adjoining the same maximum
singleton makes their parent spectra unequal.  Both seven-vertex parents are
decomposable and contain no strong six-set.
-/

namespace ErdosSzekeres
namespace TurnLanguageCollision

open RankProfileCollision

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def leftLowerTree : DecompositionTree 7 :=
  .node
    (.node
      (.node (.node (.leaf 5) (.leaf 3)) (.leaf 0))
      (.node (.leaf 2) (.leaf 1)))
    (.leaf 4)

def rightLowerTree : DecompositionTree 7 :=
  .node
    (.node
      (.leaf 3)
      (.node (.node (.node (.leaf 5) (.leaf 2)) (.leaf 0)) (.leaf 1)))
    (.leaf 4)

def leftTree : DecompositionTree 7 := .node leftLowerTree (.leaf 6)

def rightTree : DecompositionTree 7 := .node rightLowerTree (.leaf 6)

def leftColor : TripleColoring 7 := leftTree.coloring

def rightColor : TripleColoring 7 := rightTree.coloring

def lower : Finset (Fin 7) := Finset.univ.erase 6

theorem left_decomposable : IsDecomposable leftColor := by
  have hwell : leftTree.WellFormed := by
    simp [leftTree, leftLowerTree, DecompositionTree.WellFormed,
      DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn leftTree hwell
  have hvertices : leftTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem right_decomposable : IsDecomposable rightColor := by
  have hwell : rightTree.WellFormed := by
    simp [rightTree, rightLowerTree, DecompositionTree.WellFormed,
      DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn rightTree hwell
  have hvertices : rightTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem left_root : HasDeepBelowSplit leftColor lower {6} := by
  have h := DecompositionTree.node_split leftLowerTree
    (DecompositionTree.leaf 6) (by decide)
  have hlower : leftLowerTree.vertices = lower := by decide
  rw [hlower] at h
  exact h

theorem right_root : HasDeepBelowSplit rightColor lower {6} := by
  have h := DecompositionTree.node_split rightLowerTree
    (DecompositionTree.leaf 6) (by decide)
  have hlower : rightLowerTree.vertices = lower := by decide
  rw [hlower] at h
  exact h

theorem left_noStrongSetBool_six :
    ∀ s : Finset (Fin 7), s.card = 6 →
      strongPolygonSetBool leftColor s = false := by
  decide

theorem right_noStrongSetBool_six :
    ∀ s : Finset (Fin 7), s.card = 6 →
      strongPolygonSetBool rightColor s = false := by
  decide

theorem left_open :
    ¬∃ f : Fin 6 ↪o Fin 7, IsStrongPolygonOn leftColor f := by
  rintro ⟨f, hstrong⟩
  let s : Finset (Fin 7) := Finset.univ.image f
  have hcard : s.card = 6 := by
    simpa [s] using Finset.card_image_of_injective Finset.univ f.injective
  have hfalse := left_noStrongSetBool_six s hcard
  have htrue := (strongPolygonSetBool_eq_true_iff leftColor s).2
    (FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [hfalse] at htrue
  contradiction

theorem right_open :
    ¬∃ f : Fin 6 ↪o Fin 7, IsStrongPolygonOn rightColor f := by
  rintro ⟨f, hstrong⟩
  let s : Finset (Fin 7) := Finset.univ.image f
  have hcard : s.card = 6 := by
    simpa [s] using Finset.card_image_of_injective Finset.univ f.injective
  have hfalse := right_noStrongSetBool_six s hcard
  have htrue := (strongPolygonSetBool_eq_true_iff rightColor s).2
    (FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [hfalse] at htrue
  contradiction

/-- The endpoint-forgetting child spectra agree at the depth needed for a
six-vertex chain. -/
theorem lower_spectrum_equal :
    TurnLanguage.pairTurnSpectrum leftColor lower 4 =
      TurnLanguage.pairTurnSpectrum rightColor lower 4 := by
  decide

/-- The word `right,right,left` reaches `(5,6)` only in the first parent. -/
theorem parent_word_difference :
    [Turn.right, Turn.right, Turn.left] ∈
        TurnLanguage.pairTurnLanguage leftColor Finset.univ 4 5 6 ∧
      [Turn.right, Turn.right, Turn.left] ∉
        TurnLanguage.pairTurnLanguage rightColor Finset.univ 4 5 6 := by
  decide

theorem parent_spectrum_ne :
    TurnLanguage.pairTurnSpectrum leftColor Finset.univ 4 ≠
      TurnLanguage.pairTurnSpectrum rightColor Finset.univ 4 := by
  decide

/-- Grouping languages by their terminal endpoint repairs this particular
collision: the lower incoming-star spectra already differ. -/
theorem lower_incomingStarSpectrum_ne :
    TurnLanguage.incomingStarSpectrum leftColor lower 4 ≠
      TurnLanguage.incomingStarSpectrum rightColor lower 4 := by
  decide

end TurnLanguageCollision
end ErdosSzekeres

end
