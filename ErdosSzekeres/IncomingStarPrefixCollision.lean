module

public import ErdosSzekeres.TurnLanguageCollision

@[expose] public section

/-!
# An open depth-three incoming-star prefix collision

The global incoming-star spectrum does not determine its prefix spectra in
general.  These open decomposable eight-vertex colorings agree globally at
depth three but differ at the cut before vertex seven.  At depth four their
global spectra are already different, so this is a negative control rather
than a counterexample to the live `k = 6`, depth-four candidate.
-/

namespace ErdosSzekeres
namespace IncomingStarPrefixCollision

open RankProfileCollision

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def leftTree : DecompositionTree 8 :=
  .node
    (.node (.node (.leaf 7) (.leaf 0)) (.node (.leaf 4) (.leaf 2)))
    (.node (.node (.node (.leaf 6) (.leaf 5)) (.leaf 3)) (.leaf 1))

def rightTree : DecompositionTree 8 :=
  .node
    (.node (.node (.leaf 6) (.leaf 0)) (.node (.leaf 4) (.leaf 2)))
    (.node (.node (.node (.leaf 7) (.leaf 5)) (.leaf 3)) (.leaf 1))

def leftColor : TripleColoring 8 := leftTree.coloring

def rightColor : TripleColoring 8 := rightTree.coloring

theorem color_ne : leftColor ≠ rightColor := by
  intro h
  let t : OrderedTriple 8 := ⟨0, 2, 6, by decide, by decide⟩
  have h026 := congrFun h t
  have hleft : leftColor t = Turn.left := by decide
  have hright : rightColor t = Turn.right := by decide
  rw [hleft, hright] at h026
  exact Turn.noConfusion h026

theorem left_decomposable : IsDecomposable leftColor := by
  have hwell : leftTree.WellFormed := by
    simp [leftTree, DecompositionTree.WellFormed, DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn leftTree hwell
  have hvertices : leftTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem right_decomposable : IsDecomposable rightColor := by
  have hwell : rightTree.WellFormed := by
    simp [rightTree, DecompositionTree.WellFormed, DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn rightTree hwell
  have hvertices : rightTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem left_noStrongSetBool_five :
    ∀ s : Finset (Fin 8), s.card = 5 →
      strongPolygonSetBool leftColor s = false := by
  decide

theorem right_noStrongSetBool_five :
    ∀ s : Finset (Fin 8), s.card = 5 →
      strongPolygonSetBool rightColor s = false := by
  decide

theorem left_open :
    ¬∃ f : Fin 5 ↪o Fin 8, IsStrongPolygonOn leftColor f := by
  rintro ⟨f, hstrong⟩
  let s : Finset (Fin 8) := Finset.univ.image f
  have hcard : s.card = 5 := by
    simpa [s] using Finset.card_image_of_injective Finset.univ f.injective
  have hfalse := left_noStrongSetBool_five s hcard
  have htrue := (strongPolygonSetBool_eq_true_iff leftColor s).2
    (FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [hfalse] at htrue
  contradiction

theorem right_open :
    ¬∃ f : Fin 5 ↪o Fin 8, IsStrongPolygonOn rightColor f := by
  rintro ⟨f, hstrong⟩
  let s : Finset (Fin 8) := Finset.univ.image f
  have hcard : s.card = 5 := by
    simpa [s] using Finset.card_image_of_injective Finset.univ f.injective
  have hfalse := right_noStrongSetBool_five s hcard
  have htrue := (strongPolygonSetBool_eq_true_iff rightColor s).2
    (FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [hfalse] at htrue
  contradiction

theorem depth_three_spectrum_equal :
    TurnLanguage.incomingStarSpectrum leftColor Finset.univ 3 =
      TurnLanguage.incomingStarSpectrum rightColor Finset.univ 3 := by
  decide

theorem depth_three_prefix_ne :
    TurnLanguage.prefixIncomingStarSpectrum leftColor Finset.univ 3 7 ≠
      TurnLanguage.prefixIncomingStarSpectrum rightColor Finset.univ 3 7 := by
  decide

theorem depth_four_spectrum_ne :
    TurnLanguage.incomingStarSpectrum leftColor Finset.univ 4 ≠
      TurnLanguage.incomingStarSpectrum rightColor Finset.univ 4 := by
  decide

end IncomingStarPrefixCollision
end ErdosSzekeres

end
