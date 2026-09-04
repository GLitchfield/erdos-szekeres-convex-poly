module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 075. -/

theorem fin15Anchored_fiveFamily_mask07723 :
    (({0, 1, 3, 5, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 11, 12}, {3, 9, 10, 11, 12}, {3, 5, 10, 11, 12}, {3, 5, 9, 11, 12}, {3, 5, 9, 10, 12}, {3, 5, 9, 10, 11}, {1, 9, 10, 11, 12}, {1, 5, 10, 11, 12}, {1, 5, 9, 11, 12}, {1, 5, 9, 10, 12}, {1, 5, 9, 10, 11}, {1, 3, 10, 11, 12}, {1, 3, 9, 11, 12}, {1, 3, 9, 10, 12}, {1, 3, 9, 10, 11}, {1, 3, 5, 11, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 10, 11}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 11}, {1, 3, 5, 9, 10}, {0, 9, 10, 11, 12}, {0, 5, 10, 11, 12}, {0, 5, 9, 11, 12}, {0, 5, 9, 10, 12}, {0, 5, 9, 10, 11}, {0, 3, 10, 11, 12}, {0, 3, 9, 11, 12}, {0, 3, 9, 10, 12}, {0, 3, 9, 10, 11}, {0, 3, 5, 11, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 10, 11}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 11}, {0, 3, 5, 9, 10}, {0, 1, 10, 11, 12}, {0, 1, 9, 11, 12}, {0, 1, 9, 10, 12}, {0, 1, 9, 10, 11}, {0, 1, 5, 11, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 10, 11}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 11}, {0, 1, 5, 9, 10}, {0, 1, 3, 11, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 10, 11}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 11}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 11}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07723 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {1, 9, 10, 11, 12} ∨
        polygon = {1, 5, 10, 11, 12} ∨
        polygon = {1, 5, 9, 11, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 11} ∨
        polygon = {1, 3, 10, 11, 12} ∨
        polygon = {1, 3, 9, 11, 12} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 9, 10, 11} ∨
        polygon = {1, 3, 5, 11, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 10, 11} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 11} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 5, 9, 11, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 11} ∨
        polygon = {0, 3, 10, 11, 12} ∨
        polygon = {0, 3, 9, 11, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 3, 5, 11, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 10, 11} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 11} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 9, 11, 12} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 9, 10, 11} ∨
        polygon = {0, 1, 5, 11, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 10, 11} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 11} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 3, 11, 12} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 11} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 11} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07723] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13867 :
    (({0, 1, 3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {0, 9, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13867 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13867] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22059 :
    (({0, 1, 3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {0, 9, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22059 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22059] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26155 :
    (({0, 1, 3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {0, 9, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26155 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26155] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29227 :
    (({0, 1, 3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {0, 9, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29227 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29227] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29739 :
    (({0, 1, 3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 10, 12, 14}, {1, 5, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {0, 10, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29739 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29739] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01995 :
    (({0, 1, 3, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 10}, {3, 7, 8, 9, 10}, {3, 6, 8, 9, 10}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {1, 7, 8, 9, 10}, {1, 6, 8, 9, 10}, {1, 6, 7, 9, 10}, {1, 6, 7, 8, 10}, {1, 6, 7, 8, 9}, {1, 3, 8, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 7, 8, 10}, {1, 3, 7, 8, 9}, {1, 3, 6, 9, 10}, {1, 3, 6, 8, 10}, {1, 3, 6, 8, 9}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 6, 7, 8}, {0, 7, 8, 9, 10}, {0, 6, 8, 9, 10}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 3, 8, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 1, 8, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}, {0, 1, 6, 9, 10}, {0, 1, 6, 8, 10}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01995 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 10} ∨
        polygon = {1, 6, 8, 9, 10} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01995] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05067 :
    (({0, 1, 3, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 12}, {3, 7, 8, 9, 12}, {3, 6, 8, 9, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}, {1, 7, 8, 9, 12}, {1, 6, 8, 9, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 8, 12}, {1, 6, 7, 8, 9}, {1, 3, 8, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 9}, {1, 3, 6, 9, 12}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 9}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 6, 7, 8}, {0, 7, 8, 9, 12}, {0, 6, 8, 9, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 3, 8, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 1, 8, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 9}, {0, 1, 6, 9, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 3, 9, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05067 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 12} ∨
        polygon = {1, 6, 8, 9, 12} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 6, 7, 8, 12} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 8, 12} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05067] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09163 :
    (({0, 1, 3, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 13}, {3, 7, 8, 9, 13}, {3, 6, 8, 9, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 9}, {1, 7, 8, 9, 13}, {1, 6, 8, 9, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 8, 13}, {1, 6, 7, 8, 9}, {1, 3, 8, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 9}, {1, 3, 6, 9, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 9}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {1, 3, 6, 7, 8}, {0, 7, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 9}, {0, 3, 8, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 9}, {0, 3, 6, 9, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 1, 8, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 9}, {0, 1, 6, 9, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09163 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 13} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 8, 13} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09163] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17355 :
    (({0, 1, 3, 6, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 14}, {3, 7, 8, 9, 14}, {3, 6, 8, 9, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 9}, {1, 7, 8, 9, 14}, {1, 6, 8, 9, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 8, 14}, {1, 6, 7, 8, 9}, {1, 3, 8, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 9}, {1, 3, 6, 9, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 8, 9}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 9}, {1, 3, 6, 7, 8}, {0, 7, 8, 9, 14}, {0, 6, 8, 9, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 9}, {0, 3, 8, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 9}, {0, 3, 6, 9, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 1, 8, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 9}, {0, 1, 6, 9, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 3, 9, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17355 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 9, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 14} ∨
        polygon = {1, 6, 8, 9, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17355] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05579 :
    (({0, 1, 3, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {3, 7, 8, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {1, 7, 8, 10, 12}, {1, 6, 8, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 8, 12}, {1, 6, 7, 8, 10}, {1, 3, 8, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 10}, {1, 3, 6, 10, 12}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 10}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 8}, {0, 7, 8, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 3, 8, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}, {0, 1, 8, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 10}, {0, 1, 6, 10, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 10}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 8}, {0, 1, 3, 10, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05579 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 12} ∨
        polygon = {1, 6, 8, 10, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 8, 12} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 8, 12} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05579] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09675 :
    (({0, 1, 3, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 13}, {3, 7, 8, 10, 13}, {3, 6, 8, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 10}, {1, 7, 8, 10, 13}, {1, 6, 8, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 8, 13}, {1, 6, 7, 8, 10}, {1, 3, 8, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 10}, {1, 3, 6, 10, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 10}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 8}, {0, 7, 8, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 3, 8, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 6, 10, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}, {0, 1, 8, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 10}, {0, 1, 6, 10, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 10}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 8}, {0, 1, 3, 10, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09675 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 13} ∨
        polygon = {1, 6, 8, 10, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 8, 13} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09675] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17867 :
    (({0, 1, 3, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 14}, {3, 7, 8, 10, 14}, {3, 6, 8, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 10}, {1, 7, 8, 10, 14}, {1, 6, 8, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 8, 14}, {1, 6, 7, 8, 10}, {1, 3, 8, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 10}, {1, 3, 6, 10, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 8, 10}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 8}, {0, 7, 8, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 10}, {0, 3, 8, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 10}, {0, 3, 6, 10, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}, {0, 1, 8, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 10}, {0, 1, 6, 10, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 10}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 8}, {0, 1, 3, 10, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17867 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 14} ∨
        polygon = {1, 6, 8, 10, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 3, 8, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17867] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20939 :
    (({0, 1, 3, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 12, 14}, {3, 7, 8, 12, 14}, {3, 6, 8, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 12}, {1, 7, 8, 12, 14}, {1, 6, 8, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 8, 14}, {1, 6, 7, 8, 12}, {1, 3, 8, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 8, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 8}, {0, 7, 8, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 3, 8, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 12}, {0, 3, 6, 12, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 12}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 8}, {0, 1, 8, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 12}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 8}, {0, 1, 3, 12, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20939 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {1, 7, 8, 12, 14} ∨
        polygon = {1, 6, 8, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 6, 7, 8, 12} ∨
        polygon = {1, 3, 8, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 8, 12} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20939] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25035 :
    (({0, 1, 3, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 13, 14}, {3, 7, 8, 13, 14}, {3, 6, 8, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 13}, {1, 7, 8, 13, 14}, {1, 6, 8, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 8, 14}, {1, 6, 7, 8, 13}, {1, 3, 8, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 8, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 8}, {0, 7, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}, {0, 3, 8, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 13}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 8}, {0, 1, 8, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 8}, {0, 1, 3, 13, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25035 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {1, 7, 8, 13, 14} ∨
        polygon = {1, 6, 8, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 6, 7, 8, 13} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25035] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05835 :
    (({0, 1, 3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {0, 7, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05835 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05835] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09931 :
    (({0, 1, 3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {0, 7, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09931 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09931] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18123 :
    (({0, 1, 3, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {0, 7, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18123 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18123] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13003 :
    (({0, 1, 3, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {0, 7, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13003 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13003] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21195 :
    (({0, 1, 3, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {0, 7, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21195 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21195] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25291 :
    (({0, 1, 3, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {1, 7, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {0, 7, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25291 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25291] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13515 :
    (({0, 1, 3, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {1, 7, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {0, 7, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13515 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13515] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21707 :
    (({0, 1, 3, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {1, 7, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {0, 7, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21707 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21707] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25803 :
    (({0, 1, 3, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {1, 7, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {0, 7, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25803 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25803] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28875 :
    (({0, 1, 3, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {1, 7, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {0, 7, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28875 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28875] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05963 :
    (({0, 1, 3, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 12}, {3, 8, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {1, 8, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 8, 10, 12}, {1, 6, 8, 9, 12}, {1, 6, 8, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 8, 10, 12}, {1, 3, 8, 9, 12}, {1, 3, 8, 9, 10}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 10}, {1, 3, 6, 8, 9}, {0, 8, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 1, 9, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 8, 9, 12}, {0, 1, 8, 9, 10}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 10}, {0, 1, 6, 8, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05963 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 12} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 6, 8, 10, 12} ∨
        polygon = {1, 6, 8, 9, 12} ∨
        polygon = {1, 6, 8, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 8, 12} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05963] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10059 :
    (({0, 1, 3, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 13}, {3, 8, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 10}, {1, 8, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 8, 10, 13}, {1, 6, 8, 9, 13}, {1, 6, 8, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 10}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 10}, {1, 3, 6, 8, 9}, {0, 8, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 1, 9, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 9, 13}, {0, 1, 8, 9, 10}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 10}, {0, 1, 6, 8, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10059 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 8, 10, 13} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 6, 8, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10059] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25419 :
    (({0, 1, 3, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 13, 14}, {3, 8, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 8, 13, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 13}, {1, 8, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 8, 13, 14}, {1, 6, 8, 9, 14}, {1, 6, 8, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 8, 9, 14}, {1, 3, 8, 9, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 8, 14}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 9}, {0, 8, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 9}, {0, 1, 9, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25419 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {1, 8, 9, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 8, 13, 14} ∨
        polygon = {1, 6, 8, 9, 14} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25419] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13899 :
    (({0, 1, 3, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 9, 10, 13}, {1, 6, 9, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {0, 9, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13899 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13899] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22091 :
    (({0, 1, 3, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {0, 9, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22091 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22091] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26187 :
    (({0, 1, 3, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {0, 9, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26187 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26187] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29259 :
    (({0, 1, 3, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {0, 9, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29259 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29259] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29771 :
    (({0, 1, 3, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 10, 12, 14}, {1, 6, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {0, 10, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29771 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 6, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29771] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10123 :
    (({0, 1, 3, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {3, 8, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 10}, {1, 8, 9, 10, 13}, {1, 7, 9, 10, 13}, {1, 7, 8, 10, 13}, {1, 7, 8, 9, 13}, {1, 7, 8, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 10}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 10}, {1, 3, 7, 8, 9}, {0, 8, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 1, 9, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 9, 13}, {0, 1, 8, 9, 10}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10123 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 8, 10, 13} ∨
        polygon = {1, 7, 8, 9, 13} ∨
        polygon = {1, 7, 8, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10123] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18315 :
    (({0, 1, 3, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {3, 8, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 10}, {1, 8, 9, 10, 14}, {1, 7, 9, 10, 14}, {1, 7, 8, 10, 14}, {1, 7, 8, 9, 14}, {1, 7, 8, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 8, 10, 14}, {1, 3, 8, 9, 14}, {1, 3, 8, 9, 10}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 10}, {1, 3, 7, 8, 9}, {0, 8, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 1, 9, 10, 14}, {0, 1, 8, 10, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 10}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18315 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 8, 10, 14} ∨
        polygon = {1, 7, 8, 9, 14} ∨
        polygon = {1, 7, 8, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 8, 10, 14} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 8, 10, 14} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18315] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask07819 :
    (({0, 1, 3, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 11, 12}, {3, 9, 10, 11, 12}, {3, 7, 10, 11, 12}, {3, 7, 9, 11, 12}, {3, 7, 9, 10, 12}, {3, 7, 9, 10, 11}, {1, 9, 10, 11, 12}, {1, 7, 10, 11, 12}, {1, 7, 9, 11, 12}, {1, 7, 9, 10, 12}, {1, 7, 9, 10, 11}, {1, 3, 10, 11, 12}, {1, 3, 9, 11, 12}, {1, 3, 9, 10, 12}, {1, 3, 9, 10, 11}, {1, 3, 7, 11, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 10, 11}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 11}, {1, 3, 7, 9, 10}, {0, 9, 10, 11, 12}, {0, 7, 10, 11, 12}, {0, 7, 9, 11, 12}, {0, 7, 9, 10, 12}, {0, 7, 9, 10, 11}, {0, 3, 10, 11, 12}, {0, 3, 9, 11, 12}, {0, 3, 9, 10, 12}, {0, 3, 9, 10, 11}, {0, 3, 7, 11, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 10, 11}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 11}, {0, 3, 7, 9, 10}, {0, 1, 10, 11, 12}, {0, 1, 9, 11, 12}, {0, 1, 9, 10, 12}, {0, 1, 9, 10, 11}, {0, 1, 7, 11, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 10, 11}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 11}, {0, 1, 7, 9, 10}, {0, 1, 3, 11, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 10, 11}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 11}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 11}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07819 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 7, 9, 11, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {1, 9, 10, 11, 12} ∨
        polygon = {1, 7, 10, 11, 12} ∨
        polygon = {1, 7, 9, 11, 12} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 7, 9, 10, 11} ∨
        polygon = {1, 3, 10, 11, 12} ∨
        polygon = {1, 3, 9, 11, 12} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 9, 10, 11} ∨
        polygon = {1, 3, 7, 11, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 10, 11} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 11} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 7, 9, 11, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 11} ∨
        polygon = {0, 3, 10, 11, 12} ∨
        polygon = {0, 3, 9, 11, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 3, 7, 11, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 10, 11} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 11} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 9, 11, 12} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 9, 10, 11} ∨
        polygon = {0, 1, 7, 11, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 11} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 11, 12} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 11} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 11} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07819] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask11915 :
    (({0, 1, 3, 7, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 11, 13}, {3, 9, 10, 11, 13}, {3, 7, 10, 11, 13}, {3, 7, 9, 11, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 11}, {1, 9, 10, 11, 13}, {1, 7, 10, 11, 13}, {1, 7, 9, 11, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 11}, {1, 3, 10, 11, 13}, {1, 3, 9, 11, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 11}, {1, 3, 7, 11, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 11}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 11}, {1, 3, 7, 9, 10}, {0, 9, 10, 11, 13}, {0, 7, 10, 11, 13}, {0, 7, 9, 11, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 11}, {0, 3, 10, 11, 13}, {0, 3, 9, 11, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 11}, {0, 3, 7, 11, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 11}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 11}, {0, 3, 7, 9, 10}, {0, 1, 10, 11, 13}, {0, 1, 9, 11, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 11}, {0, 1, 7, 11, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 11}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 11}, {0, 1, 7, 9, 10}, {0, 1, 3, 11, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 11}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 11}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 11}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask11915 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 9, 10, 11, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 11, 13} ∨
        polygon = {3, 9, 10, 11, 13} ∨
        polygon = {3, 7, 10, 11, 13} ∨
        polygon = {3, 7, 9, 11, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {1, 9, 10, 11, 13} ∨
        polygon = {1, 7, 10, 11, 13} ∨
        polygon = {1, 7, 9, 11, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 11} ∨
        polygon = {1, 3, 10, 11, 13} ∨
        polygon = {1, 3, 9, 11, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 11} ∨
        polygon = {1, 3, 7, 11, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 11} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 11} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 7, 10, 11, 13} ∨
        polygon = {0, 7, 9, 11, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 11} ∨
        polygon = {0, 3, 10, 11, 13} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 3, 7, 11, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 11} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 11} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 1, 10, 11, 13} ∨
        polygon = {0, 1, 9, 11, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 11} ∨
        polygon = {0, 1, 7, 11, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 11} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 11, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 11} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 11} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask11915] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13963 :
    (({0, 1, 3, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 7, 9, 12, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13963 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13963] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22155 :
    (({0, 1, 3, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22155 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22155] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26251 :
    (({0, 1, 3, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26251 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26251] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
