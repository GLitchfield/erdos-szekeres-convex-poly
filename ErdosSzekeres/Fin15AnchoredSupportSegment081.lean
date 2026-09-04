module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 081. -/

theorem fin15Anchored_fiveFamily_mask04829 :
    (({0, 2, 3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {3, 6, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {0, 6, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 2, 7, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04829 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04829] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08925 :
    (({0, 2, 3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {3, 6, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {0, 6, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 2, 7, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08925 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08925] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17117 :
    (({0, 2, 3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {3, 6, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {0, 6, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 2, 7, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 2, 3, 9, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17117 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17117] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05341 :
    (({0, 2, 3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {3, 6, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {2, 6, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {2, 3, 7, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {0, 6, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 3, 7, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 2, 7, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05341 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05341] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09437 :
    (({0, 2, 3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {3, 6, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {2, 6, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {2, 3, 7, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {0, 6, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 3, 7, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 2, 7, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09437 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09437] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17629 :
    (({0, 2, 3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {3, 6, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {2, 6, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}, {2, 3, 7, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {0, 6, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 3, 7, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 2, 7, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 2, 3, 10, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17629 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17629] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12509 :
    (({0, 2, 3, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 13}, {3, 6, 7, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {2, 6, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {2, 3, 7, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}, {0, 6, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 3, 7, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 2, 7, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12509 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12509] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20701 :
    (({0, 2, 3, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 14}, {3, 6, 7, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {2, 6, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 12}, {2, 3, 7, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}, {0, 6, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 3, 7, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 2, 7, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}, {0, 2, 3, 12, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20701 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20701] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24797 :
    (({0, 2, 3, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 13, 14}, {3, 6, 7, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {2, 6, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}, {2, 3, 7, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 7}, {0, 6, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 3, 7, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 7}, {0, 2, 7, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 7}, {0, 2, 3, 13, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24797 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24797] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05725 :
    (({0, 2, 3, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {2, 6, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {0, 6, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 2, 9, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05725 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05725] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09821 :
    (({0, 2, 3, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {2, 6, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {0, 6, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 2, 9, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09821 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09821] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18013 :
    (({0, 2, 3, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {2, 6, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {0, 6, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 2, 9, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18013 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18013] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10845 :
    (({0, 2, 3, 4, 6, 9, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 11, 13}, {3, 6, 9, 11, 13}, {3, 4, 9, 11, 13}, {3, 4, 6, 11, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 11}, {2, 6, 9, 11, 13}, {2, 4, 9, 11, 13}, {2, 4, 6, 11, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 11}, {2, 3, 9, 11, 13}, {2, 3, 6, 11, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 11}, {2, 3, 4, 11, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 11}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 11}, {2, 3, 4, 6, 9}, {0, 6, 9, 11, 13}, {0, 4, 9, 11, 13}, {0, 4, 6, 11, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 11}, {0, 3, 9, 11, 13}, {0, 3, 6, 11, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 11}, {0, 3, 4, 11, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 11}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 11}, {0, 3, 4, 6, 9}, {0, 2, 9, 11, 13}, {0, 2, 6, 11, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 11}, {0, 2, 4, 11, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 11}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 11}, {0, 2, 4, 6, 9}, {0, 2, 3, 11, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 11}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 11}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10845 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 9, 11, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 11, 13} ∨
        polygon = {3, 6, 9, 11, 13} ∨
        polygon = {3, 4, 9, 11, 13} ∨
        polygon = {3, 4, 6, 11, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {2, 6, 9, 11, 13} ∨
        polygon = {2, 4, 9, 11, 13} ∨
        polygon = {2, 4, 6, 11, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 3, 9, 11, 13} ∨
        polygon = {2, 3, 6, 11, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 4, 11, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 11, 13} ∨
        polygon = {0, 4, 9, 11, 13} ∨
        polygon = {0, 4, 6, 11, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 11} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 6, 11, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 11} ∨
        polygon = {0, 3, 4, 11, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 11} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 11} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 6, 11, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 11} ∨
        polygon = {0, 2, 4, 11, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 11} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 11} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 11, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 11} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 11} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 9, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10845] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12893 :
    (({0, 2, 3, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {2, 6, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {0, 6, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 2, 9, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12893 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12893] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21085 :
    (({0, 2, 3, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {2, 6, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {0, 6, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 2, 9, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21085 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21085] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25181 :
    (({0, 2, 3, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {2, 6, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {0, 6, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 2, 9, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25181 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25181] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13405 :
    (({0, 2, 3, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {2, 6, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {0, 6, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 2, 10, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13405 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13405] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21597 :
    (({0, 2, 3, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {2, 6, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {0, 6, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 2, 10, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21597 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21597] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25693 :
    (({0, 2, 3, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {2, 6, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {0, 6, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 2, 10, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25693 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25693] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28765 :
    (({0, 2, 3, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {2, 6, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {0, 6, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 2, 12, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28765 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28765] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05789 :
    (({0, 2, 3, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {0, 7, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 2, 9, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05789 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05789] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09885 :
    (({0, 2, 3, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {0, 7, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 2, 9, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09885 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09885] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18077 :
    (({0, 2, 3, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {0, 7, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 2, 9, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18077 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18077] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12957 :
    (({0, 2, 3, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {0, 7, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 2, 9, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12957 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12957] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21149 :
    (({0, 2, 3, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {0, 7, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 2, 9, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21149 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21149] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25245 :
    (({0, 2, 3, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {0, 7, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 2, 9, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25245 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25245] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13469 :
    (({0, 2, 3, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {0, 7, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 2, 10, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13469 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13469] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21661 :
    (({0, 2, 3, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {0, 7, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 2, 10, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21661 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21661] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25757 :
    (({0, 2, 3, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {0, 7, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 2, 10, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25757 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25757] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28829 :
    (({0, 2, 3, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {0, 7, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 2, 12, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28829 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28829] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask11805 :
    (({0, 2, 3, 4, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 11, 13}, {3, 9, 10, 11, 13}, {3, 4, 10, 11, 13}, {3, 4, 9, 11, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 11}, {2, 9, 10, 11, 13}, {2, 4, 10, 11, 13}, {2, 4, 9, 11, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 11}, {2, 3, 10, 11, 13}, {2, 3, 9, 11, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 11}, {2, 3, 4, 11, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 11}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 11}, {2, 3, 4, 9, 10}, {0, 9, 10, 11, 13}, {0, 4, 10, 11, 13}, {0, 4, 9, 11, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 11}, {0, 3, 10, 11, 13}, {0, 3, 9, 11, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 11}, {0, 3, 4, 11, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 11}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 11}, {0, 3, 4, 9, 10}, {0, 2, 10, 11, 13}, {0, 2, 9, 11, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 11}, {0, 2, 4, 11, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 11}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 11}, {0, 2, 4, 9, 10}, {0, 2, 3, 11, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 11}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 11}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask11805 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 9, 10, 11, 13} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 11, 13} ∨
        polygon = {3, 9, 10, 11, 13} ∨
        polygon = {3, 4, 10, 11, 13} ∨
        polygon = {3, 4, 9, 11, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {2, 9, 10, 11, 13} ∨
        polygon = {2, 4, 10, 11, 13} ∨
        polygon = {2, 4, 9, 11, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 3, 10, 11, 13} ∨
        polygon = {2, 3, 9, 11, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 3, 4, 11, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 4, 10, 11, 13} ∨
        polygon = {0, 4, 9, 11, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 11} ∨
        polygon = {0, 3, 10, 11, 13} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 3, 4, 11, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 11} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 11} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 2, 10, 11, 13} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 11} ∨
        polygon = {0, 2, 4, 11, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 11} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 11} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 3, 11, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 11} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 11} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask11805] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13853 :
    (({0, 2, 3, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {0, 9, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13853 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13853] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22045 :
    (({0, 2, 3, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {0, 9, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22045 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22045] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26141 :
    (({0, 2, 3, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {0, 9, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26141 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26141] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14877 :
    (({0, 2, 3, 4, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 11, 12, 13}, {3, 9, 11, 12, 13}, {3, 4, 11, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 11, 13}, {3, 4, 9, 11, 12}, {2, 9, 11, 12, 13}, {2, 4, 11, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 11, 13}, {2, 4, 9, 11, 12}, {2, 3, 11, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 11, 13}, {2, 3, 9, 11, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 11, 13}, {2, 3, 4, 11, 12}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 11}, {0, 9, 11, 12, 13}, {0, 4, 11, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 11, 13}, {0, 4, 9, 11, 12}, {0, 3, 11, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 11, 13}, {0, 3, 9, 11, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 11, 13}, {0, 3, 4, 11, 12}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 11}, {0, 2, 11, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 11, 13}, {0, 2, 9, 11, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 11, 13}, {0, 2, 4, 11, 12}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 11}, {0, 2, 3, 12, 13}, {0, 2, 3, 11, 13}, {0, 2, 3, 11, 12}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 11}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14877 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 9, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 9, 11, 12, 13} ∨
        polygon = {3, 9, 11, 12, 13} ∨
        polygon = {3, 4, 11, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 11, 13} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {2, 9, 11, 12, 13} ∨
        polygon = {2, 4, 11, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 11, 13} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 3, 11, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 11, 13} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 11, 13} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 4, 11, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 9, 11, 13} ∨
        polygon = {0, 4, 9, 11, 12} ∨
        polygon = {0, 3, 11, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 9, 11, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 11, 13} ∨
        polygon = {0, 3, 4, 11, 12} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 11} ∨
        polygon = {0, 2, 11, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 11, 13} ∨
        polygon = {0, 2, 4, 11, 12} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 11} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 11, 13} ∨
        polygon = {0, 2, 3, 11, 12} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 11} ∨
        polygon = {0, 2, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14877] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask23069 :
    (({0, 2, 3, 4, 9, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 11, 12, 14}, {3, 9, 11, 12, 14}, {3, 4, 11, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 11, 14}, {3, 4, 9, 11, 12}, {2, 9, 11, 12, 14}, {2, 4, 11, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 11, 14}, {2, 4, 9, 11, 12}, {2, 3, 11, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 11, 14}, {2, 3, 9, 11, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 11, 14}, {2, 3, 4, 11, 12}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 11}, {0, 9, 11, 12, 14}, {0, 4, 11, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 11, 14}, {0, 4, 9, 11, 12}, {0, 3, 11, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 11, 14}, {0, 3, 9, 11, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 11, 14}, {0, 3, 4, 11, 12}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 11}, {0, 2, 11, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 11, 14}, {0, 2, 9, 11, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 11, 14}, {0, 2, 4, 11, 12}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 11}, {0, 2, 3, 12, 14}, {0, 2, 3, 11, 14}, {0, 2, 3, 11, 12}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 11}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask23069 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 9, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 11, 12, 14} ∨
        polygon = {3, 9, 11, 12, 14} ∨
        polygon = {3, 4, 11, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 11, 14} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {2, 9, 11, 12, 14} ∨
        polygon = {2, 4, 11, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 11, 14} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 3, 11, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 11, 14} ∨
        polygon = {2, 3, 9, 11, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 11, 14} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {0, 9, 11, 12, 14} ∨
        polygon = {0, 4, 11, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 11, 14} ∨
        polygon = {0, 4, 9, 11, 12} ∨
        polygon = {0, 3, 11, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 11, 14} ∨
        polygon = {0, 3, 9, 11, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 11, 14} ∨
        polygon = {0, 3, 4, 11, 12} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 11} ∨
        polygon = {0, 2, 11, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 11, 14} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 11, 14} ∨
        polygon = {0, 2, 4, 11, 12} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 11} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 11, 14} ∨
        polygon = {0, 2, 3, 11, 12} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 11} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 11} ∨
        polygon = {0, 2, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 9, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask23069] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29213 :
    (({0, 2, 3, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {0, 9, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29213 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29213] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29725 :
    (({0, 2, 3, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {0, 10, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29725 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29725] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01773 :
    (({0, 2, 3, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {3, 6, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}, {2, 6, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {2, 3, 7, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {0, 6, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 2, 7, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01773 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01773] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04845 :
    (({0, 2, 3, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {3, 6, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}, {2, 6, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}, {2, 3, 7, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {0, 6, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 2, 7, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04845 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04845] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
