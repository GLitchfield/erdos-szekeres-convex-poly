module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 082. -/

theorem fin15Anchored_fiveFamily_mask08941 :
    (({0, 2, 3, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {3, 6, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 9}, {2, 6, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 9}, {2, 3, 7, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 9}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {0, 6, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 2, 7, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08941 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08941] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17133 :
    (({0, 2, 3, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {3, 6, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 9}, {2, 6, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 9}, {2, 3, 7, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 9}, {2, 3, 5, 9, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {0, 6, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 2, 7, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 2, 3, 9, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17133 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17133] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05357 :
    (({0, 2, 3, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {3, 6, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {2, 6, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {2, 3, 7, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {0, 6, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 3, 7, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 2, 7, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05357 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05357] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09453 :
    (({0, 2, 3, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {3, 6, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}, {2, 6, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {2, 3, 7, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {0, 6, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 3, 7, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 2, 7, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09453 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09453] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17645 :
    (({0, 2, 3, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {3, 6, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 10}, {2, 6, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 10}, {2, 3, 7, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {0, 6, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 3, 7, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 2, 7, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 10}, {0, 2, 5, 10, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 2, 3, 10, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17645 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17645] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12525 :
    (({0, 2, 3, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {3, 6, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {2, 6, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {2, 3, 7, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}, {0, 6, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 3, 7, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 2, 7, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12525 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12525] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20717 :
    (({0, 2, 3, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {3, 6, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}, {2, 6, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {2, 3, 7, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}, {0, 6, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 3, 7, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 2, 7, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 5, 12, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}, {0, 2, 3, 12, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20717 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20717] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24813 :
    (({0, 2, 3, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {3, 6, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {2, 6, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 3, 7, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 7}, {0, 6, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 3, 7, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 7}, {0, 2, 7, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 7}, {0, 2, 3, 13, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24813 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24813] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05741 :
    (({0, 2, 3, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {2, 6, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {0, 6, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 2, 9, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05741 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05741] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09837 :
    (({0, 2, 3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {2, 6, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {0, 6, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 2, 9, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09837 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09837] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18029 :
    (({0, 2, 3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}, {2, 6, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {0, 6, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 2, 9, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 10}, {0, 2, 5, 10, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18029 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18029] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12909 :
    (({0, 2, 3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {2, 6, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {0, 6, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 2, 9, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12909 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12909] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21101 :
    (({0, 2, 3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {2, 6, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {0, 6, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 2, 9, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}, {0, 2, 5, 12, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21101 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21101] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25197 :
    (({0, 2, 3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {2, 6, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {0, 6, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 2, 9, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25197 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25197] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13421 :
    (({0, 2, 3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {2, 6, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {0, 6, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 2, 10, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13421 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13421] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21613 :
    (({0, 2, 3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {2, 6, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {0, 6, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 2, 10, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21613 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21613] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25709 :
    (({0, 2, 3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {2, 6, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {0, 6, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 2, 10, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25709 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25709] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28781 :
    (({0, 2, 3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {2, 6, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {0, 6, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 2, 12, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28781 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28781] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09645 :
    (({0, 2, 3, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 13}, {3, 7, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}, {2, 7, 8, 10, 13}, {2, 5, 8, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 8, 13}, {2, 5, 7, 8, 10}, {2, 3, 8, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 8, 13}, {2, 3, 7, 8, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 8, 13}, {2, 3, 5, 8, 10}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 8}, {0, 7, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 3, 8, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 2, 8, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 8, 13}, {0, 2, 7, 8, 10}, {0, 2, 5, 10, 13}, {0, 2, 5, 8, 13}, {0, 2, 5, 8, 10}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 8}, {0, 2, 3, 10, 13}, {0, 2, 3, 8, 13}, {0, 2, 3, 8, 10}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 8}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 8}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09645 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {2, 7, 8, 10, 13} ∨
        polygon = {2, 5, 8, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 8, 13} ∨
        polygon = {2, 5, 7, 8, 10} ∨
        polygon = {2, 3, 8, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 8, 13} ∨
        polygon = {2, 3, 7, 8, 10} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 8, 13} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 8} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 2, 8, 10, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 8, 13} ∨
        polygon = {0, 2, 7, 8, 10} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 8, 13} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 8} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 8, 13} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 8} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 8} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09645] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05805 :
    (({0, 2, 3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {0, 7, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 2, 9, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05805 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05805] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09901 :
    (({0, 2, 3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {0, 7, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 2, 9, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09901 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09901] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18093 :
    (({0, 2, 3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {0, 7, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 2, 9, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 10}, {0, 2, 5, 10, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18093 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18093] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12973 :
    (({0, 2, 3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {0, 7, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 2, 9, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12973 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12973] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21165 :
    (({0, 2, 3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {0, 7, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 2, 9, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 5, 12, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21165 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21165] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25261 :
    (({0, 2, 3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {0, 7, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 2, 9, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25261 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25261] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13485 :
    (({0, 2, 3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {0, 7, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 2, 10, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13485 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13485] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21677 :
    (({0, 2, 3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {0, 7, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 2, 10, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21677 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21677] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25773 :
    (({0, 2, 3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {0, 7, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 2, 10, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25773 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25773] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28845 :
    (({0, 2, 3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {0, 7, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 2, 12, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28845 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28845] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13613 :
    (({0, 2, 3, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {2, 8, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 8, 12, 13}, {2, 5, 8, 10, 13}, {2, 5, 8, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 8, 12, 13}, {2, 3, 8, 10, 13}, {2, 3, 8, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 8, 13}, {2, 3, 5, 8, 12}, {2, 3, 5, 8, 10}, {0, 8, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 2, 10, 12, 13}, {0, 2, 8, 12, 13}, {0, 2, 8, 10, 13}, {0, 2, 8, 10, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 8, 13}, {0, 2, 5, 8, 12}, {0, 2, 5, 8, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 8, 13}, {0, 2, 3, 8, 12}, {0, 2, 3, 8, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13613 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {2, 8, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 8, 12, 13} ∨
        polygon = {2, 5, 8, 10, 13} ∨
        polygon = {2, 5, 8, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 8, 12, 13} ∨
        polygon = {2, 3, 8, 10, 13} ∨
        polygon = {2, 3, 8, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 8, 13} ∨
        polygon = {2, 3, 5, 8, 12} ∨
        polygon = {2, 3, 5, 8, 10} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 8, 12, 13} ∨
        polygon = {0, 2, 8, 10, 13} ∨
        polygon = {0, 2, 8, 10, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 8, 13} ∨
        polygon = {0, 2, 5, 8, 12} ∨
        polygon = {0, 2, 5, 8, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 8, 13} ∨
        polygon = {0, 2, 3, 8, 12} ∨
        polygon = {0, 2, 3, 8, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13613] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask07725 :
    (({0, 2, 3, 5, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 11, 12}, {3, 9, 10, 11, 12}, {3, 5, 10, 11, 12}, {3, 5, 9, 11, 12}, {3, 5, 9, 10, 12}, {3, 5, 9, 10, 11}, {2, 9, 10, 11, 12}, {2, 5, 10, 11, 12}, {2, 5, 9, 11, 12}, {2, 5, 9, 10, 12}, {2, 5, 9, 10, 11}, {2, 3, 10, 11, 12}, {2, 3, 9, 11, 12}, {2, 3, 9, 10, 12}, {2, 3, 9, 10, 11}, {2, 3, 5, 11, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 10, 11}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 11}, {2, 3, 5, 9, 10}, {0, 9, 10, 11, 12}, {0, 5, 10, 11, 12}, {0, 5, 9, 11, 12}, {0, 5, 9, 10, 12}, {0, 5, 9, 10, 11}, {0, 3, 10, 11, 12}, {0, 3, 9, 11, 12}, {0, 3, 9, 10, 12}, {0, 3, 9, 10, 11}, {0, 3, 5, 11, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 10, 11}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 11}, {0, 3, 5, 9, 10}, {0, 2, 10, 11, 12}, {0, 2, 9, 11, 12}, {0, 2, 9, 10, 12}, {0, 2, 9, 10, 11}, {0, 2, 5, 11, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 10, 11}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 11}, {0, 2, 5, 9, 10}, {0, 2, 3, 11, 12}, {0, 2, 3, 10, 12}, {0, 2, 3, 10, 11}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 11}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 11}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07725 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 9, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
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
        polygon = {0, 2, 10, 11, 12} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 9, 10, 11} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 11} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 11, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 10, 11} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 11} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07725] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask11821 :
    (({0, 2, 3, 5, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 11, 13}, {3, 9, 10, 11, 13}, {3, 5, 10, 11, 13}, {3, 5, 9, 11, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 11}, {2, 9, 10, 11, 13}, {2, 5, 10, 11, 13}, {2, 5, 9, 11, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 11}, {2, 3, 10, 11, 13}, {2, 3, 9, 11, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 11}, {2, 3, 5, 11, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 11}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 11}, {2, 3, 5, 9, 10}, {0, 9, 10, 11, 13}, {0, 5, 10, 11, 13}, {0, 5, 9, 11, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 11}, {0, 3, 10, 11, 13}, {0, 3, 9, 11, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 11}, {0, 3, 5, 11, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 11}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 11}, {0, 3, 5, 9, 10}, {0, 2, 10, 11, 13}, {0, 2, 9, 11, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 11}, {0, 2, 5, 11, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 11}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 11}, {0, 2, 5, 9, 10}, {0, 2, 3, 11, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 11}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 11}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 11}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask11821 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 9, 10, 11, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 11, 13} ∨
        polygon = {3, 9, 10, 11, 13} ∨
        polygon = {3, 5, 10, 11, 13} ∨
        polygon = {3, 5, 9, 11, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {2, 9, 10, 11, 13} ∨
        polygon = {2, 5, 10, 11, 13} ∨
        polygon = {2, 5, 9, 11, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 3, 10, 11, 13} ∨
        polygon = {2, 3, 9, 11, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 3, 5, 11, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 5, 10, 11, 13} ∨
        polygon = {0, 5, 9, 11, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 11} ∨
        polygon = {0, 3, 10, 11, 13} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 3, 5, 11, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 11} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 11} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 2, 10, 11, 13} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 11} ∨
        polygon = {0, 2, 5, 11, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 11} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 11, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 11} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 11} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask11821] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13869 :
    (({0, 2, 3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {0, 9, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13869 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
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
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13869] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22061 :
    (({0, 2, 3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {0, 9, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22061 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
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
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22061] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26157 :
    (({0, 2, 3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {0, 9, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26157 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
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
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26157] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14893 :
    (({0, 2, 3, 5, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 11, 12, 13}, {3, 9, 11, 12, 13}, {3, 5, 11, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 11, 13}, {3, 5, 9, 11, 12}, {2, 9, 11, 12, 13}, {2, 5, 11, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 11, 13}, {2, 5, 9, 11, 12}, {2, 3, 11, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 11, 13}, {2, 3, 9, 11, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 11, 13}, {2, 3, 5, 11, 12}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 11}, {0, 9, 11, 12, 13}, {0, 5, 11, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 11, 13}, {0, 5, 9, 11, 12}, {0, 3, 11, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 11, 13}, {0, 3, 9, 11, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 11, 13}, {0, 3, 5, 11, 12}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 11}, {0, 2, 11, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 11, 13}, {0, 2, 9, 11, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 11, 13}, {0, 2, 5, 11, 12}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 11}, {0, 2, 3, 12, 13}, {0, 2, 3, 11, 13}, {0, 2, 3, 11, 12}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 11}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 11}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14893 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 9, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 11, 12, 13} ∨
        polygon = {3, 9, 11, 12, 13} ∨
        polygon = {3, 5, 11, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 11, 13} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {2, 9, 11, 12, 13} ∨
        polygon = {2, 5, 11, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 11, 13} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 3, 11, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 11, 13} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 11, 13} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 5, 11, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 11, 13} ∨
        polygon = {0, 5, 9, 11, 12} ∨
        polygon = {0, 3, 11, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 9, 11, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 11, 13} ∨
        polygon = {0, 3, 5, 11, 12} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 11} ∨
        polygon = {0, 2, 11, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 11, 13} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 11} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 11, 13} ∨
        polygon = {0, 2, 3, 11, 12} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 11} ∨
        polygon = {0, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14893] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29229 :
    (({0, 2, 3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {0, 9, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29229 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
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
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29229] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29741 :
    (({0, 2, 3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {0, 10, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29741 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
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
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29741] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05837 :
    (({0, 2, 3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {0, 7, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 2, 9, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05837 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
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
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05837] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09933 :
    (({0, 2, 3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {0, 7, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 2, 9, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09933 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
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
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09933] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
