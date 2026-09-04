module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 074. -/

theorem fin15Anchored_fiveFamily_mask09451 :
    (({0, 1, 3, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {3, 6, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}, {1, 6, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}, {1, 3, 7, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 7}, {0, 6, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 3, 7, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 1, 7, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09451 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09451] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17643 :
    (({0, 1, 3, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {3, 6, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 10}, {1, 6, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 10}, {1, 3, 7, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 5, 10, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 7}, {0, 6, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 3, 7, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 1, 7, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 3, 10, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17643 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17643] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12523 :
    (({0, 1, 3, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {3, 6, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {1, 6, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 3, 7, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 7}, {0, 6, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 3, 7, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 1, 7, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12523 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12523] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20715 :
    (({0, 1, 3, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {3, 6, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}, {1, 6, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}, {1, 3, 7, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 7}, {0, 6, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 3, 7, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}, {0, 1, 7, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 3, 12, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20715 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20715] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24811 :
    (({0, 1, 3, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {3, 6, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {1, 6, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}, {1, 3, 7, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 7}, {0, 6, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 3, 7, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 7}, {0, 1, 7, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 7}, {0, 1, 3, 13, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24811 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24811] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09067 :
    (({0, 1, 3, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 13}, {3, 6, 8, 9, 13}, {3, 5, 8, 9, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 9}, {1, 6, 8, 9, 13}, {1, 5, 8, 9, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 8, 13}, {1, 5, 6, 8, 9}, {1, 3, 8, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 9}, {1, 3, 5, 9, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 9}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 8}, {0, 6, 8, 9, 13}, {0, 5, 8, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 9}, {0, 3, 8, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 9}, {0, 3, 5, 9, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 9}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 8}, {0, 1, 8, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 9}, {0, 1, 5, 9, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 9}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 8}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09067 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 5, 8, 9, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 8, 13} ∨
        polygon = {1, 5, 6, 8, 9} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 9} ∨
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
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09067] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05483 :
    (({0, 1, 3, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 12}, {3, 6, 8, 10, 12}, {3, 5, 8, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 10}, {1, 6, 8, 10, 12}, {1, 5, 8, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 8, 12}, {1, 5, 6, 8, 10}, {1, 3, 8, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 10}, {1, 3, 5, 10, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 10}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 8}, {0, 6, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 3, 8, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 1, 8, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 8}, {0, 1, 3, 10, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05483 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {1, 6, 8, 10, 12} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 8, 12} ∨
        polygon = {1, 5, 6, 8, 10} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 8, 12} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
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
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05483] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09579 :
    (({0, 1, 3, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 13}, {3, 6, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 10}, {1, 6, 8, 10, 13}, {1, 5, 8, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 8, 13}, {1, 5, 6, 8, 10}, {1, 3, 8, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 10}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 8}, {0, 6, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 3, 8, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 1, 8, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 10}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 8}, {0, 1, 3, 10, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09579 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {1, 6, 8, 10, 13} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 8, 13} ∨
        polygon = {1, 5, 6, 8, 10} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
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
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09579] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24939 :
    (({0, 1, 3, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 13, 14}, {3, 6, 8, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 13}, {1, 6, 8, 13, 14}, {1, 5, 8, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 8, 14}, {1, 5, 6, 8, 13}, {1, 3, 8, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 8, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 8}, {0, 6, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 3, 8, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 8}, {0, 1, 8, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 8}, {0, 1, 3, 13, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 8}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24939 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {1, 6, 8, 13, 14} ∨
        polygon = {1, 5, 8, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 8, 14} ∨
        polygon = {1, 5, 6, 8, 13} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
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
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24939] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05739 :
    (({0, 1, 3, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {1, 6, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {0, 6, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 1, 9, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05739 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
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
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05739] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09835 :
    (({0, 1, 3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {1, 6, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {0, 6, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 1, 9, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09835 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09835] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18027 :
    (({0, 1, 3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}, {1, 6, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {0, 6, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 1, 9, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18027 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
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
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18027] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12907 :
    (({0, 1, 3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {1, 6, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {0, 6, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 1, 9, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12907 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
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
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12907] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21099 :
    (({0, 1, 3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {1, 6, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {0, 6, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 1, 9, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21099 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
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
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21099] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25195 :
    (({0, 1, 3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {1, 6, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}, {0, 6, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 1, 9, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25195 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 9} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25195] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13419 :
    (({0, 1, 3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {1, 6, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {0, 6, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 1, 10, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13419 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13419] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21611 :
    (({0, 1, 3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {1, 6, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {0, 6, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 1, 10, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21611 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21611] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25707 :
    (({0, 1, 3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {1, 6, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {0, 6, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 1, 10, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25707 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25707] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28779 :
    (({0, 1, 3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {1, 6, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {0, 6, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 1, 12, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28779 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28779] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01963 :
    (({0, 1, 3, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 10}, {3, 7, 8, 9, 10}, {3, 5, 8, 9, 10}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}, {1, 7, 8, 9, 10}, {1, 5, 8, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 7, 8, 10}, {1, 5, 7, 8, 9}, {1, 3, 8, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 7, 8, 10}, {1, 3, 7, 8, 9}, {1, 3, 5, 9, 10}, {1, 3, 5, 8, 10}, {1, 3, 5, 8, 9}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 3, 5, 7, 8}, {0, 7, 8, 9, 10}, {0, 5, 8, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 3, 8, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 1, 8, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}, {0, 1, 5, 9, 10}, {0, 1, 5, 8, 10}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01963 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 10} ∨
        polygon = {1, 5, 8, 9, 10} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
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
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01963] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05035 :
    (({0, 1, 3, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 12}, {3, 7, 8, 9, 12}, {3, 5, 8, 9, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 9}, {1, 7, 8, 9, 12}, {1, 5, 8, 9, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 8, 12}, {1, 5, 7, 8, 9}, {1, 3, 8, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 9}, {1, 3, 5, 9, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 9}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 3, 5, 7, 8}, {0, 7, 8, 9, 12}, {0, 5, 8, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}, {0, 3, 8, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 1, 8, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 9}, {0, 1, 5, 9, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 3, 9, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05035 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 12} ∨
        polygon = {1, 5, 8, 9, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 7, 8, 12} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
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
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05035] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09131 :
    (({0, 1, 3, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 13}, {3, 7, 8, 9, 13}, {3, 5, 8, 9, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 9}, {1, 7, 8, 9, 13}, {1, 5, 8, 9, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 8, 13}, {1, 5, 7, 8, 9}, {1, 3, 8, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 9}, {1, 3, 5, 9, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 9}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {1, 3, 5, 7, 8}, {0, 7, 8, 9, 13}, {0, 5, 8, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 9}, {0, 3, 8, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 1, 8, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 9}, {0, 1, 5, 9, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09131 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 13} ∨
        polygon = {1, 5, 8, 9, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 8, 13} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 9} ∨
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
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09131] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17323 :
    (({0, 1, 3, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 14}, {3, 7, 8, 9, 14}, {3, 5, 8, 9, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 9}, {1, 7, 8, 9, 14}, {1, 5, 8, 9, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 8, 14}, {1, 5, 7, 8, 9}, {1, 3, 8, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 9}, {1, 3, 5, 9, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 9}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 9}, {1, 3, 5, 7, 8}, {0, 7, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 9}, {0, 3, 8, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 9}, {0, 3, 5, 9, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 1, 8, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 9}, {0, 1, 5, 9, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 3, 9, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17323 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 8, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 14} ∨
        polygon = {1, 5, 8, 9, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 8, 14} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 9} ∨
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
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17323] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05547 :
    (({0, 1, 3, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 12}, {3, 7, 8, 10, 12}, {3, 5, 8, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {1, 7, 8, 10, 12}, {1, 5, 8, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 8, 12}, {1, 5, 7, 8, 10}, {1, 3, 8, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 10}, {1, 3, 5, 10, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 10}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 8}, {0, 7, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 3, 8, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 1, 8, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 8}, {0, 1, 3, 10, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05547 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 12} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 8, 12} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
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
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05547] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09643 :
    (({0, 1, 3, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 13}, {3, 7, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}, {1, 7, 8, 10, 13}, {1, 5, 8, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 8, 13}, {1, 5, 7, 8, 10}, {1, 3, 8, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 10}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 8}, {0, 7, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 3, 8, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 1, 8, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 10}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 8}, {0, 1, 3, 10, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09643 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 13} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 8, 13} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 8} ∨
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
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09643] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25003 :
    (({0, 1, 3, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 13, 14}, {3, 7, 8, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {1, 7, 8, 13, 14}, {1, 5, 8, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 8, 14}, {1, 5, 7, 8, 13}, {1, 3, 8, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 8}, {0, 7, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 3, 8, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 8}, {0, 1, 8, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 8}, {0, 1, 3, 13, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 8}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25003 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {1, 7, 8, 13, 14} ∨
        polygon = {1, 5, 8, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 8, 14} ∨
        polygon = {1, 5, 7, 8, 13} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
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
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25003] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05803 :
    (({0, 1, 3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {1, 7, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {0, 7, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05803 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
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
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05803] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09899 :
    (({0, 1, 3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {1, 7, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {0, 7, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09899 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09899] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18091 :
    (({0, 1, 3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {1, 7, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {0, 7, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18091 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
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
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18091] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12971 :
    (({0, 1, 3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {1, 7, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {0, 7, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12971 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
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
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12971] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21163 :
    (({0, 1, 3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {1, 7, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {0, 7, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21163 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
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
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21163] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25259 :
    (({0, 1, 3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {1, 7, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {0, 7, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25259 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 9} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25259] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13483 :
    (({0, 1, 3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {1, 7, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {0, 7, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13483 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13483] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21675 :
    (({0, 1, 3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {1, 7, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {0, 7, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21675 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21675] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25771 :
    (({0, 1, 3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {1, 7, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {0, 7, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25771 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25771] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22699 :
    (({0, 1, 3, 5, 7, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 11, 12, 14}, {3, 7, 11, 12, 14}, {3, 5, 11, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 11, 14}, {3, 5, 7, 11, 12}, {1, 7, 11, 12, 14}, {1, 5, 11, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 11, 14}, {1, 5, 7, 11, 12}, {1, 3, 11, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 11, 14}, {1, 3, 7, 11, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 11, 14}, {1, 3, 5, 11, 12}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 11}, {0, 7, 11, 12, 14}, {0, 5, 11, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 11, 14}, {0, 5, 7, 11, 12}, {0, 3, 11, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 11, 14}, {0, 3, 7, 11, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 11, 14}, {0, 3, 5, 11, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 11}, {0, 1, 11, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 11, 14}, {0, 1, 7, 11, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 11, 14}, {0, 1, 5, 11, 12}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 11}, {0, 1, 3, 12, 14}, {0, 1, 3, 11, 14}, {0, 1, 3, 11, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 11}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 11}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22699 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 11, 12, 14} ∨
        polygon = {3, 7, 11, 12, 14} ∨
        polygon = {3, 5, 11, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 11, 14} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {1, 7, 11, 12, 14} ∨
        polygon = {1, 5, 11, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 11, 14} ∨
        polygon = {1, 5, 7, 11, 12} ∨
        polygon = {1, 3, 11, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 11, 14} ∨
        polygon = {1, 3, 7, 11, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 11, 14} ∨
        polygon = {1, 3, 5, 11, 12} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 11} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 11, 14} ∨
        polygon = {0, 5, 7, 11, 12} ∨
        polygon = {0, 3, 11, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 11, 14} ∨
        polygon = {0, 3, 7, 11, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 11, 14} ∨
        polygon = {0, 3, 5, 11, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 11} ∨
        polygon = {0, 1, 11, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 11, 14} ∨
        polygon = {0, 1, 7, 11, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 11, 14} ∨
        polygon = {0, 1, 5, 11, 12} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 11} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 11, 14} ∨
        polygon = {0, 1, 3, 11, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 11} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 11} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22699] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28843 :
    (({0, 1, 3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {1, 7, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {0, 7, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28843 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28843] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05931 :
    (({0, 1, 3, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 12}, {3, 8, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {1, 8, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 8, 10, 12}, {1, 5, 8, 9, 12}, {1, 5, 8, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 8, 10, 12}, {1, 3, 8, 9, 12}, {1, 3, 8, 9, 10}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 10}, {1, 3, 5, 8, 9}, {0, 8, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 1, 9, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 8, 9, 12}, {0, 1, 8, 9, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 5, 8, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05931 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 5, 8, 9, 12} ∨
        polygon = {1, 5, 8, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05931] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25387 :
    (({0, 1, 3, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 13, 14}, {3, 8, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 13}, {1, 8, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 8, 13, 14}, {1, 5, 8, 9, 14}, {1, 5, 8, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 8, 9, 14}, {1, 3, 8, 9, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 9}, {0, 8, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 9}, {0, 1, 9, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25387 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {1, 8, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 8, 13, 14} ∨
        polygon = {1, 5, 8, 9, 14} ∨
        polygon = {1, 5, 8, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25387] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13611 :
    (({0, 1, 3, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {1, 8, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 8, 12, 13}, {1, 5, 8, 10, 13}, {1, 5, 8, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 10}, {0, 8, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 1, 10, 12, 13}, {0, 1, 8, 12, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13611 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {1, 8, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 8, 12, 13} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 8, 12, 13} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 10} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 8, 12, 13} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13611] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
