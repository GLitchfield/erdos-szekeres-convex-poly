module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 080. -/

theorem fin15Anchored_fiveFamily_mask31875 :
    (({0, 1, 7, 10, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{10, 11, 12, 13, 14}, {7, 11, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 10, 11, 13, 14}, {7, 10, 11, 12, 14}, {7, 10, 11, 12, 13}, {1, 11, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 10, 11, 13, 14}, {1, 10, 11, 12, 14}, {1, 10, 11, 12, 13}, {1, 7, 12, 13, 14}, {1, 7, 11, 13, 14}, {1, 7, 11, 12, 14}, {1, 7, 11, 12, 13}, {1, 7, 10, 13, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 12, 13}, {1, 7, 10, 11, 14}, {1, 7, 10, 11, 13}, {1, 7, 10, 11, 12}, {0, 11, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 10, 11, 13, 14}, {0, 10, 11, 12, 14}, {0, 10, 11, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 11, 13, 14}, {0, 7, 11, 12, 14}, {0, 7, 11, 12, 13}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 10, 11, 14}, {0, 7, 10, 11, 13}, {0, 7, 10, 11, 12}, {0, 1, 12, 13, 14}, {0, 1, 11, 13, 14}, {0, 1, 11, 12, 14}, {0, 1, 11, 12, 13}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 10, 11, 14}, {0, 1, 10, 11, 13}, {0, 1, 10, 11, 12}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 7, 11, 14}, {0, 1, 7, 11, 13}, {0, 1, 7, 11, 12}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 7, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask31875 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 7, 10, 11, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {10, 11, 12, 13, 14} ∨
        polygon = {7, 11, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 10, 11, 13, 14} ∨
        polygon = {7, 10, 11, 12, 14} ∨
        polygon = {7, 10, 11, 12, 13} ∨
        polygon = {1, 11, 12, 13, 14} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 10, 11, 13, 14} ∨
        polygon = {1, 10, 11, 12, 14} ∨
        polygon = {1, 10, 11, 12, 13} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 11, 13, 14} ∨
        polygon = {1, 7, 11, 12, 14} ∨
        polygon = {1, 7, 11, 12, 13} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 7, 10, 11, 14} ∨
        polygon = {1, 7, 10, 11, 13} ∨
        polygon = {1, 7, 10, 11, 12} ∨
        polygon = {0, 11, 12, 13, 14} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 10, 11, 13, 14} ∨
        polygon = {0, 10, 11, 12, 14} ∨
        polygon = {0, 10, 11, 12, 13} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 11, 13, 14} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 7, 11, 12, 13} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 10, 11, 14} ∨
        polygon = {0, 7, 10, 11, 13} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 11, 13, 14} ∨
        polygon = {0, 1, 11, 12, 14} ∨
        polygon = {0, 1, 11, 12, 13} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 10, 11, 14} ∨
        polygon = {0, 1, 10, 11, 13} ∨
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 11, 14} ∨
        polygon = {0, 1, 7, 11, 13} ∨
        polygon = {0, 1, 7, 11, 12} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 10, 11} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 7, 10, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask31875] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00765 :
    (({0, 2, 3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {3, 5, 6, 7, 9}, {3, 4, 6, 7, 9}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 9}, {2, 4, 6, 7, 9}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 9}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {0, 5, 6, 7, 9}, {0, 4, 6, 7, 9}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 9}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 2, 6, 7, 9}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00765 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00765] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01277 :
    (({0, 2, 3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {3, 5, 6, 7, 10}, {3, 4, 6, 7, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 10}, {2, 4, 6, 7, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {0, 5, 6, 7, 10}, {0, 4, 6, 7, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 2, 6, 7, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01277 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01277] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04349 :
    (({0, 2, 3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {3, 5, 6, 7, 12}, {3, 4, 6, 7, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 12}, {2, 4, 6, 7, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {0, 5, 6, 7, 12}, {0, 4, 6, 7, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 2, 6, 7, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04349 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04349] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08445 :
    (({0, 2, 3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {3, 5, 6, 7, 13}, {3, 4, 6, 7, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 13}, {2, 4, 6, 7, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {0, 5, 6, 7, 13}, {0, 4, 6, 7, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 2, 6, 7, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 2, 3, 7, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08445 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 7, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08445] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16637 :
    (({0, 2, 3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {3, 5, 6, 7, 14}, {3, 4, 6, 7, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 14}, {2, 4, 6, 7, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {0, 5, 6, 7, 14}, {0, 4, 6, 7, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 7}, {0, 3, 6, 7, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 7}, {0, 3, 4, 7, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}, {0, 2, 6, 7, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 2, 3, 7, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16637 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 7, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16637] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08573 :
    (({0, 2, 3, 4, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 13}, {3, 5, 6, 8, 13}, {3, 4, 6, 8, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 8}, {2, 5, 6, 8, 13}, {2, 4, 6, 8, 13}, {2, 4, 5, 8, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 8}, {2, 3, 6, 8, 13}, {2, 3, 5, 8, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 8}, {2, 3, 4, 8, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 8}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 8}, {2, 3, 4, 5, 6}, {0, 5, 6, 8, 13}, {0, 4, 6, 8, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 8}, {0, 3, 6, 8, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 8}, {0, 3, 4, 8, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}, {0, 2, 6, 8, 13}, {0, 2, 5, 8, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 8}, {0, 2, 4, 8, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 8}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 8}, {0, 2, 4, 5, 6}, {0, 2, 3, 8, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 8}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 8}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 8}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08573 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 8, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {2, 5, 6, 8, 13} ∨
        polygon = {2, 4, 6, 8, 13} ∨
        polygon = {2, 4, 5, 8, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 8} ∨
        polygon = {2, 3, 6, 8, 13} ∨
        polygon = {2, 3, 5, 8, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 8} ∨
        polygon = {2, 3, 4, 8, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 8} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 8, 13} ∨
        polygon = {0, 2, 5, 8, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 8} ∨
        polygon = {0, 2, 4, 8, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 8} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 8} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 8, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 8} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 8} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 8} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08573] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01661 :
    (({0, 2, 3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {3, 5, 6, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {0, 5, 6, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 2, 6, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01661 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01661] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04733 :
    (({0, 2, 3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {3, 5, 6, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {0, 5, 6, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 2, 6, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04733 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04733] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08829 :
    (({0, 2, 3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {3, 5, 6, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {0, 5, 6, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 2, 6, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 2, 3, 9, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08829 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08829] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17021 :
    (({0, 2, 3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {3, 5, 6, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {0, 5, 6, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 9}, {0, 3, 6, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 9}, {0, 3, 4, 9, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}, {0, 2, 6, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 2, 3, 9, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17021 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17021] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05245 :
    (({0, 2, 3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {3, 5, 6, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {2, 5, 6, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 3, 6, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}, {0, 5, 6, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 3, 6, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}, {0, 2, 6, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05245 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05245] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09341 :
    (({0, 2, 3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {3, 5, 6, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {2, 5, 6, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {2, 3, 6, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}, {0, 5, 6, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 3, 6, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}, {0, 2, 6, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 2, 3, 10, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09341 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09341] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17533 :
    (({0, 2, 3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {3, 5, 6, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {2, 5, 6, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}, {2, 3, 6, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}, {0, 5, 6, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 3, 6, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}, {0, 2, 6, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 2, 3, 10, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17533 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17533] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12413 :
    (({0, 2, 3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {3, 5, 6, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {2, 5, 6, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 3, 6, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 6}, {0, 5, 6, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 3, 6, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 6}, {0, 2, 6, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 6}, {0, 2, 3, 12, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12413 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12413] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20605 :
    (({0, 2, 3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {3, 5, 6, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {2, 5, 6, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 3, 6, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 6}, {0, 5, 6, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 3, 6, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 6}, {0, 2, 6, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 6}, {0, 2, 3, 12, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20605 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20605] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24701 :
    (({0, 2, 3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {3, 5, 6, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {2, 5, 6, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 3, 6, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 6}, {0, 5, 6, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 3, 6, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 6}, {0, 2, 6, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 6}, {0, 2, 3, 13, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 6}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24701 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 6, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 6} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 6} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24701] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01725 :
    (({0, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {0, 5, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 2, 7, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01725 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01725] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04797 :
    (({0, 2, 3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {0, 5, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 2, 7, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04797 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04797] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08893 :
    (({0, 2, 3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {0, 5, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 2, 7, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08893 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08893] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17085 :
    (({0, 2, 3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {0, 5, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}, {0, 3, 7, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 3, 4, 9, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}, {0, 2, 7, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 2, 3, 9, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17085 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17085] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05309 :
    (({0, 2, 3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {2, 5, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 3, 7, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {0, 5, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 3, 7, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 2, 7, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05309 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05309] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09405 :
    (({0, 2, 3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {2, 5, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {2, 3, 7, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {0, 5, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 3, 7, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 2, 7, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09405 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09405] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17597 :
    (({0, 2, 3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {2, 5, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}, {2, 3, 7, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {0, 5, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 3, 7, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}, {0, 2, 7, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 2, 3, 10, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17597 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17597] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask06333 :
    (({0, 2, 3, 4, 5, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 11, 12}, {3, 5, 7, 11, 12}, {3, 4, 7, 11, 12}, {3, 4, 5, 11, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 11}, {2, 5, 7, 11, 12}, {2, 4, 7, 11, 12}, {2, 4, 5, 11, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 11}, {2, 3, 7, 11, 12}, {2, 3, 5, 11, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 11}, {2, 3, 4, 11, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 11}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 11}, {2, 3, 4, 5, 7}, {0, 5, 7, 11, 12}, {0, 4, 7, 11, 12}, {0, 4, 5, 11, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 11}, {0, 3, 7, 11, 12}, {0, 3, 5, 11, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 11}, {0, 3, 4, 11, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 11}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 11}, {0, 3, 4, 5, 7}, {0, 2, 7, 11, 12}, {0, 2, 5, 11, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 11}, {0, 2, 4, 11, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 11}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 11}, {0, 2, 4, 5, 7}, {0, 2, 3, 11, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 11}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 11}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06333 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 4, 7, 11, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 3, 7, 11, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 11, 12} ∨
        polygon = {0, 4, 7, 11, 12} ∨
        polygon = {0, 4, 5, 11, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 11} ∨
        polygon = {0, 3, 7, 11, 12} ∨
        polygon = {0, 3, 5, 11, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 11} ∨
        polygon = {0, 3, 4, 11, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 11} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 11} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 11, 12} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 11} ∨
        polygon = {0, 2, 4, 11, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 11} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 11} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 11, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 11} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 11} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 11} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06333] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12477 :
    (({0, 2, 3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {2, 5, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 3, 7, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {0, 5, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 3, 7, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 2, 7, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12477 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12477] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20669 :
    (({0, 2, 3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {2, 5, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 3, 7, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {0, 5, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 3, 7, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}, {0, 2, 7, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}, {0, 2, 3, 12, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20669 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20669] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24765 :
    (({0, 2, 3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {2, 5, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 3, 7, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 7}, {0, 5, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 3, 7, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 7}, {0, 2, 7, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 7}, {0, 2, 3, 13, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24765 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24765] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05693 :
    (({0, 2, 3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {2, 5, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {0, 5, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 2, 9, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05693 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05693] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09789 :
    (({0, 2, 3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {2, 5, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {0, 5, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 2, 9, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09789 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09789] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17981 :
    (({0, 2, 3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {2, 5, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {0, 5, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 2, 9, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17981 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17981] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12861 :
    (({0, 2, 3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {2, 5, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {0, 5, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 2, 9, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12861 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12861] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21053 :
    (({0, 2, 3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {2, 5, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {0, 5, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 2, 9, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21053 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21053] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25149 :
    (({0, 2, 3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {2, 5, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {0, 5, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 2, 9, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25149 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25149] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask07229 :
    (({0, 2, 3, 4, 5, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 11, 12}, {3, 5, 10, 11, 12}, {3, 4, 10, 11, 12}, {3, 4, 5, 11, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 10, 11}, {2, 5, 10, 11, 12}, {2, 4, 10, 11, 12}, {2, 4, 5, 11, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 10, 11}, {2, 3, 10, 11, 12}, {2, 3, 5, 11, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 10, 11}, {2, 3, 4, 11, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 10, 11}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 11}, {2, 3, 4, 5, 10}, {0, 5, 10, 11, 12}, {0, 4, 10, 11, 12}, {0, 4, 5, 11, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 10, 11}, {0, 3, 10, 11, 12}, {0, 3, 5, 11, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 10, 11}, {0, 3, 4, 11, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 10, 11}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 11}, {0, 3, 4, 5, 10}, {0, 2, 10, 11, 12}, {0, 2, 5, 11, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 10, 11}, {0, 2, 4, 11, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 10, 11}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 11}, {0, 2, 4, 5, 10}, {0, 2, 3, 11, 12}, {0, 2, 3, 10, 12}, {0, 2, 3, 10, 11}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 11}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 11}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07229 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 4, 10, 11, 12} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 3, 10, 11, 12} ∨
        polygon = {2, 3, 5, 11, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 4, 10, 11, 12} ∨
        polygon = {0, 4, 5, 11, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 10, 11} ∨
        polygon = {0, 3, 10, 11, 12} ∨
        polygon = {0, 3, 5, 11, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 10, 11} ∨
        polygon = {0, 3, 4, 11, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 10, 11} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 11} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 2, 10, 11, 12} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 4, 11, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 10, 11} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 11} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 3, 11, 12} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 10, 11} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 11} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 11} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07229] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13373 :
    (({0, 2, 3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {2, 5, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {0, 5, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 2, 10, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13373 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13373] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21565 :
    (({0, 2, 3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {2, 5, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {0, 5, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 2, 10, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21565 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21565] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25661 :
    (({0, 2, 3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {2, 5, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {0, 5, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 2, 10, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25661 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25661] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28733 :
    (({0, 2, 3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {2, 5, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {0, 5, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 2, 12, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28733 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 5, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28733] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01757 :
    (({0, 2, 3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {3, 6, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {0, 6, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 2, 7, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01757 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 3, 4, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01757] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
