module

public import ErdosSzekeres.TurnLanguageCollision

@[expose] public section

namespace ErdosSzekeres
namespace IncomingStarPositive

open RankProfileCollision

def leftTree : DecompositionTree 6 :=
  .node (.leaf 0)
    (.node (.leaf 3)
      (.node (.leaf 1)
        (.node (.leaf 4) (.node (.leaf 2) (.leaf 5)))))

def rightTree : DecompositionTree 6 :=
  .node (.leaf 0)
    (.node (.leaf 3)
      (.node (.leaf 4)
        (.node (.leaf 1) (.node (.leaf 2) (.leaf 5)))))

def leftColor : TripleColoring 6 := leftTree.coloring

def rightColor : TripleColoring 6 := rightTree.coloring

def upper : Finset (Fin 6) := Finset.univ.erase 0

def lower : Finset (Fin 6) := {0}

theorem color_ne : leftColor ≠ rightColor := by
  intro h
  have h145 := congrFun h
    (show OrderedTriple 6 from ⟨1, 4, 5, by decide, by decide⟩)
  norm_num [leftColor, rightColor, leftTree, rightTree,
    DecompositionTree.coloring, DecompositionTree.vertices] at h145
  simp_all

theorem child_spectrum_equal :
    TurnLanguage.incomingStarSpectrum leftColor upper 4 =
      TurnLanguage.incomingStarSpectrum rightColor upper 4 := by
  decide

theorem root_child_spectra_equal :
    (TurnLanguage.incomingStarSpectrum leftColor lower 4 =
        TurnLanguage.incomingStarSpectrum rightColor lower 4) ∧
      TurnLanguage.incomingStarSpectrum leftColor upper 4 =
        TurnLanguage.incomingStarSpectrum rightColor upper 4 := by
  exact ⟨by decide, child_spectrum_equal⟩

theorem child_prefix_equal :
    ∀ cut : Fin 6,
      TurnLanguage.prefixIncomingStarSpectrum leftColor upper 4 cut =
        TurnLanguage.prefixIncomingStarSpectrum rightColor upper 4 cut := by
  intro cut
  fin_cases cut <;> decide

theorem root_prefix_equal :
    TurnLanguage.RootRelevantPrefixEq leftColor rightColor lower upper 4 := by
  constructor
  · intro cut _
    fin_cases cut <;> decide
  · intro cut _
    exact child_prefix_equal cut

theorem parent_spectrum_equal :
    TurnLanguage.incomingStarSpectrum leftColor Finset.univ 4 =
      TurnLanguage.incomingStarSpectrum rightColor Finset.univ 4 := by
  decide

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

theorem left_noStrongSetBool_six :
    RankProfileCollision.strongPolygonSetBool leftColor Finset.univ = false := by
  decide

theorem right_noStrongSetBool_six :
    RankProfileCollision.strongPolygonSetBool rightColor Finset.univ = false := by
  decide

theorem left_open :
    ¬∃ f : Fin 6 ↪o Fin 6, IsStrongPolygonOn leftColor f := by
  rintro ⟨f, hstrong⟩
  have himage : Finset.univ.image f = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using Finset.card_image_of_injective Finset.univ f.injective
  have htrue := (RankProfileCollision.strongPolygonSetBool_eq_true_iff
    leftColor Finset.univ).2 (by
      rw [← himage]
      exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [left_noStrongSetBool_six] at htrue
  contradiction

theorem right_open :
    ¬∃ f : Fin 6 ↪o Fin 6, IsStrongPolygonOn rightColor f := by
  rintro ⟨f, hstrong⟩
  have himage : Finset.univ.image f = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using Finset.card_image_of_injective Finset.univ f.injective
  have htrue := (RankProfileCollision.strongPolygonSetBool_eq_true_iff
    rightColor Finset.univ).2 (by
      rw [← himage]
      exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [right_noStrongSetBool_six] at htrue
  contradiction

end IncomingStarPositive
end ErdosSzekeres

end
