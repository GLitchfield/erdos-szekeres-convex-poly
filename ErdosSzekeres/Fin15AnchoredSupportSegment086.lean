module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 086. -/

theorem fin15Anchored_fiveFamily_mask01785 :
    (({0, 3, 4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {4, 6, 7, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 6, 9, 10}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}, {3, 6, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}, {3, 4, 7, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {0, 6, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 3, 7, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01785 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01785] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04857 :
    (({0, 3, 4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {4, 6, 7, 9, 12}, {4, 5, 7, 9, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 9}, {3, 6, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}, {3, 4, 7, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {0, 6, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 3, 7, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04857 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04857] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08953 :
    (({0, 3, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {4, 6, 7, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 9}, {3, 6, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 9}, {3, 4, 7, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {0, 6, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 3, 7, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08953 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08953] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17145 :
    (({0, 3, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {4, 6, 7, 9, 14}, {4, 5, 7, 9, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 9}, {3, 6, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 9}, {3, 4, 7, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 9}, {3, 4, 5, 9, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {0, 6, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 3, 7, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 3, 4, 9, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17145 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17145] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05369 :
    (({0, 3, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {4, 6, 7, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {3, 6, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {3, 4, 7, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {0, 6, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 4, 7, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 3, 7, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05369 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05369] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09465 :
    (({0, 3, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {4, 6, 7, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}, {3, 6, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}, {3, 4, 7, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {0, 6, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 4, 7, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 3, 7, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09465 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09465] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17657 :
    (({0, 3, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {4, 6, 7, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 10}, {3, 6, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 10}, {3, 4, 7, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {0, 6, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 4, 7, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 3, 7, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 3, 4, 10, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17657 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17657] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12537 :
    (({0, 3, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {4, 6, 7, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}, {3, 6, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 4, 7, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}, {0, 6, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 4, 7, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}, {0, 3, 7, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12537 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12537] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20729 :
    (({0, 3, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {4, 6, 7, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}, {3, 6, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}, {3, 4, 7, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}, {0, 6, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 4, 7, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}, {0, 3, 7, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 3, 4, 12, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20729 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20729] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24825 :
    (({0, 3, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {4, 6, 7, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {3, 6, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 4, 7, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 7}, {0, 6, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 4, 7, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 7}, {0, 3, 7, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 7}, {0, 3, 4, 13, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24825 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 7} ∨
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
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24825] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01913 :
    (({0, 3, 4, 5, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 10}, {4, 6, 8, 9, 10}, {4, 5, 8, 9, 10}, {4, 5, 6, 9, 10}, {4, 5, 6, 8, 10}, {4, 5, 6, 8, 9}, {3, 6, 8, 9, 10}, {3, 5, 8, 9, 10}, {3, 5, 6, 9, 10}, {3, 5, 6, 8, 10}, {3, 5, 6, 8, 9}, {3, 4, 8, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 8}, {0, 6, 8, 9, 10}, {0, 5, 8, 9, 10}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 4, 8, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 3, 8, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 8}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01913 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01913] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04985 :
    (({0, 3, 4, 5, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 12}, {4, 6, 8, 9, 12}, {4, 5, 8, 9, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 9}, {3, 6, 8, 9, 12}, {3, 5, 8, 9, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 9}, {3, 4, 8, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 9}, {3, 4, 5, 9, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 9}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 8}, {0, 6, 8, 9, 12}, {0, 5, 8, 9, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 9}, {0, 4, 8, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 3, 8, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}, {0, 3, 5, 9, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 9}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 8}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04985 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04985] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09081 :
    (({0, 3, 4, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 13}, {4, 6, 8, 9, 13}, {4, 5, 8, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 9}, {3, 6, 8, 9, 13}, {3, 5, 8, 9, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 9}, {3, 4, 8, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 9}, {3, 4, 5, 9, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 9}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 8}, {0, 6, 8, 9, 13}, {0, 5, 8, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 9}, {0, 4, 8, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}, {0, 4, 5, 9, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 3, 8, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 9}, {0, 3, 5, 9, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 9}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 8}, {0, 3, 4, 9, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09081 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09081] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05497 :
    (({0, 3, 4, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 12}, {4, 6, 8, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 10}, {3, 6, 8, 10, 12}, {3, 5, 8, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 10}, {3, 4, 8, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 10}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 8}, {0, 6, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 4, 8, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 3, 8, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05497 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05497] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09593 :
    (({0, 3, 4, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 13}, {4, 6, 8, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 10}, {3, 6, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 10}, {3, 4, 8, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 10}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 8}, {0, 6, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 4, 8, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 3, 8, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09593 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09593] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17785 :
    (({0, 3, 4, 5, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 14}, {4, 6, 8, 10, 14}, {4, 5, 8, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 10}, {3, 6, 8, 10, 14}, {3, 5, 8, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 10}, {3, 4, 8, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 10}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 8}, {0, 6, 8, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 10}, {0, 4, 8, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 3, 8, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 3, 4, 10, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17785 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 4, 8, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17785] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12665 :
    (({0, 3, 4, 5, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 12, 13}, {4, 6, 8, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 12}, {3, 6, 8, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 12}, {3, 4, 8, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 12}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 8}, {0, 6, 8, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 4, 8, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 8}, {0, 3, 8, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 8}, {0, 3, 4, 12, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12665 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {4, 6, 8, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12665] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24953 :
    (({0, 3, 4, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 13, 14}, {4, 6, 8, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 13}, {3, 6, 8, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 13}, {3, 4, 8, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 8}, {0, 6, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 4, 8, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 8}, {0, 3, 8, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 8}, {0, 3, 4, 13, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24953 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {4, 6, 8, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24953] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05753 :
    (({0, 3, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {3, 6, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {0, 6, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 3, 9, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05753 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
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
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05753] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09849 :
    (({0, 3, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}, {3, 6, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {0, 6, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 3, 9, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09849 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
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
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09849] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18041 :
    (({0, 3, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 10}, {3, 6, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {0, 6, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 3, 9, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18041 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
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
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18041] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12921 :
    (({0, 3, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {3, 6, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {0, 6, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 3, 9, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12921 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
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
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12921] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21113 :
    (({0, 3, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 12}, {3, 6, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {3, 4, 9, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {0, 6, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 4, 9, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 3, 9, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21113 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
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
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21113] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25209 :
    (({0, 3, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {3, 6, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {0, 6, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 4, 9, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 3, 9, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25209 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
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
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25209] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13433 :
    (({0, 3, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {3, 6, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {0, 6, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 3, 10, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13433 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
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
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13433] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21625 :
    (({0, 3, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}, {3, 6, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {0, 6, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 3, 10, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21625 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
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
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21625] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25721 :
    (({0, 3, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {3, 6, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {0, 6, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 3, 10, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25721 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
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
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25721] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28793 :
    (({0, 3, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}, {3, 6, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {0, 6, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 3, 12, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28793 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
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
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28793] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01977 :
    (({0, 3, 4, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 10}, {4, 7, 8, 9, 10}, {4, 5, 8, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 7, 8, 10}, {4, 5, 7, 8, 9}, {3, 7, 8, 9, 10}, {3, 5, 8, 9, 10}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}, {3, 4, 8, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 7, 8, 10}, {3, 4, 7, 8, 9}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {3, 4, 5, 7, 8}, {0, 7, 8, 9, 10}, {0, 5, 8, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 4, 8, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 3, 8, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01977 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01977] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05049 :
    (({0, 3, 4, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 12}, {4, 7, 8, 9, 12}, {4, 5, 8, 9, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 9}, {3, 7, 8, 9, 12}, {3, 5, 8, 9, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 9}, {3, 4, 8, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 9}, {3, 4, 5, 9, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 9}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {3, 4, 5, 7, 8}, {0, 7, 8, 9, 12}, {0, 5, 8, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}, {0, 4, 8, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 3, 8, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05049 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05049] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09145 :
    (({0, 3, 4, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 13}, {4, 7, 8, 9, 13}, {4, 5, 8, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 9}, {3, 7, 8, 9, 13}, {3, 5, 8, 9, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 9}, {3, 4, 8, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 9}, {3, 4, 5, 9, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 9}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {3, 4, 5, 7, 8}, {0, 7, 8, 9, 13}, {0, 5, 8, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 9}, {0, 4, 8, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 9}, {0, 4, 5, 9, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 3, 8, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 3, 4, 9, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09145 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09145] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17337 :
    (({0, 3, 4, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 14}, {4, 7, 8, 9, 14}, {4, 5, 8, 9, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 9}, {3, 7, 8, 9, 14}, {3, 5, 8, 9, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 9}, {3, 4, 8, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 9}, {3, 4, 5, 9, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 9}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 9}, {3, 4, 5, 7, 8}, {0, 7, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 9}, {0, 4, 8, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 9}, {0, 4, 5, 9, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 3, 8, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 3, 4, 9, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17337 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17337] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05561 :
    (({0, 3, 4, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 12}, {4, 7, 8, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 10}, {3, 7, 8, 10, 12}, {3, 5, 8, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {3, 4, 8, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 10}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 8}, {0, 7, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 4, 8, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 3, 8, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05561 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05561] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09657 :
    (({0, 3, 4, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 13}, {4, 7, 8, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 10}, {3, 7, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}, {3, 4, 8, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 10}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 8}, {0, 7, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 4, 8, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 3, 8, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09657 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
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
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09657] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17849 :
    (({0, 3, 4, 5, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 14}, {4, 7, 8, 10, 14}, {4, 5, 8, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 10}, {3, 7, 8, 10, 14}, {3, 5, 8, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 10}, {3, 4, 8, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 10}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 8}, {0, 7, 8, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 10}, {0, 4, 8, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 3, 8, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 3, 4, 10, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17849 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {4, 7, 8, 10, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 4, 8, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17849] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12729 :
    (({0, 3, 4, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 12, 13}, {4, 7, 8, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 12}, {3, 7, 8, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}, {3, 4, 8, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 12}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 8}, {0, 7, 8, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 4, 8, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 8}, {0, 3, 8, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 8}, {0, 3, 4, 12, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12729 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {4, 7, 8, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12729] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20921 :
    (({0, 3, 4, 5, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 12, 14}, {4, 7, 8, 12, 14}, {4, 5, 8, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 12}, {3, 7, 8, 12, 14}, {3, 5, 8, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 12}, {3, 4, 8, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 12}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 8}, {0, 7, 8, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}, {0, 4, 8, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 8}, {0, 3, 8, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 8}, {0, 3, 4, 12, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20921 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {4, 7, 8, 12, 14} ∨
        polygon = {4, 5, 8, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 4, 8, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 4, 8, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20921] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25017 :
    (({0, 3, 4, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 13, 14}, {4, 7, 8, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 13}, {3, 7, 8, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 4, 8, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 8}, {0, 7, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 4, 8, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 8}, {0, 3, 8, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 8}, {0, 3, 4, 13, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25017 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {4, 7, 8, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25017] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05817 :
    (({0, 3, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 9, 10}, {3, 7, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {0, 7, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05817 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
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
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05817] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09913 :
    (({0, 3, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 10}, {3, 7, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {0, 7, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09913 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
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
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09913] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
