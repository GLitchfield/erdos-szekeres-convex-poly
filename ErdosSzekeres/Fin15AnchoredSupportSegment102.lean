module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 102. -/

theorem fin15Anchored_fiveFamily_mask08956 :
    (({2, 3, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {4, 6, 7, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 9}, {3, 6, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 9}, {3, 4, 7, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {2, 6, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 9}, {2, 4, 7, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 9}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {2, 3, 7, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 9}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08956 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 9, 13} →
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
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08956] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17148 :
    (({2, 3, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {4, 6, 7, 9, 14}, {4, 5, 7, 9, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 9}, {3, 6, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 9}, {3, 4, 7, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 9}, {3, 4, 5, 9, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {2, 6, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 9}, {2, 4, 7, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 9}, {2, 4, 5, 9, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {2, 3, 7, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 9}, {2, 3, 5, 9, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {2, 3, 4, 9, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17148 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 9, 14} →
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
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17148] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05372 :
    (({2, 3, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {4, 6, 7, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {3, 6, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {3, 4, 7, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {2, 6, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {2, 4, 7, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {2, 3, 7, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05372 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 10, 12} →
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
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05372] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09468 :
    (({2, 3, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {4, 6, 7, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}, {3, 6, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}, {3, 4, 7, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {2, 6, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {2, 4, 7, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {2, 3, 7, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09468 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 10, 13} →
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
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09468] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17660 :
    (({2, 3, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {4, 6, 7, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 10}, {3, 6, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 10}, {3, 4, 7, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {2, 6, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 10}, {2, 4, 7, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}, {2, 4, 5, 10, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {2, 3, 7, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {2, 3, 4, 10, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17660 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 10, 14} →
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
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17660] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12540 :
    (({2, 3, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {4, 6, 7, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}, {3, 6, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 4, 7, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}, {2, 6, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {2, 4, 7, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}, {2, 3, 7, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12540 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 12, 13} →
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
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12540] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20732 :
    (({2, 3, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {4, 6, 7, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}, {3, 6, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}, {3, 4, 7, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}, {2, 6, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {2, 4, 7, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}, {2, 3, 7, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}, {2, 3, 4, 12, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20732 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 12, 14} →
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
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20732] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24828 :
    (({2, 3, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {4, 6, 7, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {3, 6, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 4, 7, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 7}, {2, 6, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 4, 7, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 7}, {2, 3, 7, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 7}, {2, 3, 4, 13, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24828 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 7, 13, 14} →
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
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24828] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05756 :
    (({2, 3, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {3, 6, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {2, 6, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {2, 4, 9, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {2, 3, 9, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05756 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 9, 10, 12} →
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
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
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
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05756] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09852 :
    (({2, 3, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}, {3, 6, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {2, 6, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {2, 4, 9, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {2, 3, 9, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09852 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 9, 10, 13} →
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
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
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
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09852] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18044 :
    (({2, 3, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 10}, {3, 6, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {2, 6, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 10}, {2, 4, 9, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 10}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {2, 3, 9, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18044 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 9, 10, 14} →
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
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
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
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18044] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask19068 :
    (({2, 3, 4, 5, 6, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 11, 14}, {4, 6, 9, 11, 14}, {4, 5, 9, 11, 14}, {4, 5, 6, 11, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 11}, {3, 6, 9, 11, 14}, {3, 5, 9, 11, 14}, {3, 5, 6, 11, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 11}, {3, 4, 9, 11, 14}, {3, 4, 6, 11, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 11}, {3, 4, 5, 11, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 11}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 11}, {3, 4, 5, 6, 9}, {2, 6, 9, 11, 14}, {2, 5, 9, 11, 14}, {2, 5, 6, 11, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 11}, {2, 4, 9, 11, 14}, {2, 4, 6, 11, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 11}, {2, 4, 5, 11, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 11}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 11}, {2, 4, 5, 6, 9}, {2, 3, 9, 11, 14}, {2, 3, 6, 11, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 11}, {2, 3, 5, 11, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 11}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 11}, {2, 3, 5, 6, 9}, {2, 3, 4, 11, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 11}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 11}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 11}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask19068 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 9, 11, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 11, 14} ∨
        polygon = {4, 6, 9, 11, 14} ∨
        polygon = {4, 5, 9, 11, 14} ∨
        polygon = {4, 5, 6, 11, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {3, 6, 9, 11, 14} ∨
        polygon = {3, 5, 9, 11, 14} ∨
        polygon = {3, 5, 6, 11, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 11} ∨
        polygon = {3, 4, 9, 11, 14} ∨
        polygon = {3, 4, 6, 11, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 11} ∨
        polygon = {3, 4, 5, 11, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 11} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 6, 9, 11, 14} ∨
        polygon = {2, 5, 9, 11, 14} ∨
        polygon = {2, 5, 6, 11, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 4, 9, 11, 14} ∨
        polygon = {2, 4, 6, 11, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 5, 11, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 9, 11, 14} ∨
        polygon = {2, 3, 6, 11, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 11} ∨
        polygon = {2, 3, 5, 11, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 11} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 11, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 11} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask19068] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12924 :
    (({2, 3, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {3, 6, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {2, 6, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 4, 9, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {2, 3, 9, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12924 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 9, 12, 13} →
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
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
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
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12924] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21116 :
    (({2, 3, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 12}, {3, 6, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {3, 4, 9, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {2, 6, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 4, 9, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {2, 3, 9, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21116 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 9, 12, 14} →
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
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
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
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21116] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25212 :
    (({2, 3, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {3, 6, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {2, 6, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 4, 9, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}, {2, 3, 9, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25212 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 9, 13, 14} →
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
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 9} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25212] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13436 :
    (({2, 3, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {3, 6, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {2, 6, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 3, 10, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13436 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 10, 12, 13} →
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
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
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
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13436] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21628 :
    (({2, 3, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}, {3, 6, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {2, 6, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 3, 10, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21628 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 10, 12, 14} →
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
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
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
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21628] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25724 :
    (({2, 3, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {3, 6, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {2, 6, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {2, 3, 10, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25724 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 10, 13, 14} →
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
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 10} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25724] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28796 :
    (({2, 3, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}, {3, 6, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {2, 6, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 3, 12, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28796 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 6, 12, 13, 14} →
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
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 12} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28796] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask03772 :
    (({2, 3, 4, 5, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 11}, {4, 7, 9, 10, 11}, {4, 5, 9, 10, 11}, {4, 5, 7, 10, 11}, {4, 5, 7, 9, 11}, {4, 5, 7, 9, 10}, {3, 7, 9, 10, 11}, {3, 5, 9, 10, 11}, {3, 5, 7, 10, 11}, {3, 5, 7, 9, 11}, {3, 5, 7, 9, 10}, {3, 4, 9, 10, 11}, {3, 4, 7, 10, 11}, {3, 4, 7, 9, 11}, {3, 4, 7, 9, 10}, {3, 4, 5, 10, 11}, {3, 4, 5, 9, 11}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 11}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {2, 7, 9, 10, 11}, {2, 5, 9, 10, 11}, {2, 5, 7, 10, 11}, {2, 5, 7, 9, 11}, {2, 5, 7, 9, 10}, {2, 4, 9, 10, 11}, {2, 4, 7, 10, 11}, {2, 4, 7, 9, 11}, {2, 4, 7, 9, 10}, {2, 4, 5, 10, 11}, {2, 4, 5, 9, 11}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 11}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {2, 3, 9, 10, 11}, {2, 3, 7, 10, 11}, {2, 3, 7, 9, 11}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 11}, {2, 3, 5, 9, 11}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 11}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {2, 3, 4, 10, 11}, {2, 3, 4, 9, 11}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 11}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 11}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask03772 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 11} ∨
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 5, 9, 10, 11} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {3, 5, 7, 9, 11} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 11} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 5, 7, 9, 11} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 9, 10, 11} ∨
        polygon = {2, 3, 7, 10, 11} ∨
        polygon = {2, 3, 7, 9, 11} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 10, 11} ∨
        polygon = {2, 3, 5, 9, 11} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 11} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 10, 11} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 11} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask03772] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05820 :
    (({2, 3, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 9, 10}, {3, 7, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {2, 7, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {2, 4, 9, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05820 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 9, 10, 12} →
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
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
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
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05820] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09916 :
    (({2, 3, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 10}, {3, 7, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {2, 7, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}, {2, 4, 9, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09916 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 9, 10, 13} →
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
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
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
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09916] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18108 :
    (({2, 3, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 10}, {3, 7, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {2, 7, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 10}, {2, 4, 9, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 10}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18108 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
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
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18108] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12988 :
    (({2, 3, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 12}, {3, 7, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {2, 7, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 4, 9, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12988 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
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
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12988] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21180 :
    (({2, 3, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 12}, {3, 7, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {3, 4, 9, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {2, 7, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}, {2, 4, 9, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {2, 3, 9, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21180 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
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
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21180] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25276 :
    (({2, 3, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 13}, {3, 7, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {2, 7, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 4, 9, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}, {2, 3, 9, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25276 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 9} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25276] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13500 :
    (({2, 3, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 10, 12}, {3, 7, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {2, 7, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 3, 10, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13500 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
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
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13500] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21692 :
    (({2, 3, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 12}, {3, 7, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {2, 7, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 3, 10, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21692 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
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
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21692] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25788 :
    (({2, 3, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 13}, {3, 7, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {2, 7, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {2, 3, 10, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25788 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 10} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25788] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28860 :
    (({2, 3, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 12, 13}, {3, 7, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {2, 7, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 3, 12, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28860 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 12} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28860] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13884 :
    (({2, 3, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {2, 9, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13884 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
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
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13884] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22076 :
    (({2, 3, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {2, 9, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22076 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
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
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22076] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26172 :
    (({2, 3, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {2, 9, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26172 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 10} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26172] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14908 :
    (({2, 3, 4, 5, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 11, 12, 13}, {4, 9, 11, 12, 13}, {4, 5, 11, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 11, 13}, {4, 5, 9, 11, 12}, {3, 9, 11, 12, 13}, {3, 5, 11, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 11, 13}, {3, 5, 9, 11, 12}, {3, 4, 11, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 11, 13}, {3, 4, 9, 11, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 11, 13}, {3, 4, 5, 11, 12}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 11}, {2, 9, 11, 12, 13}, {2, 5, 11, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 11, 13}, {2, 5, 9, 11, 12}, {2, 4, 11, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 11, 13}, {2, 4, 9, 11, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 11, 13}, {2, 4, 5, 11, 12}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 11}, {2, 3, 11, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 11, 13}, {2, 3, 9, 11, 12}, {2, 3, 5, 12, 13}, {2, 3, 5, 11, 13}, {2, 3, 5, 11, 12}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 11}, {2, 3, 4, 12, 13}, {2, 3, 4, 11, 13}, {2, 3, 4, 11, 12}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 11}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 11}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14908 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 9, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 11, 12, 13} ∨
        polygon = {4, 9, 11, 12, 13} ∨
        polygon = {4, 5, 11, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 9, 11, 13} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {3, 9, 11, 12, 13} ∨
        polygon = {3, 5, 11, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 11, 13} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 4, 11, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 11, 13} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 11, 13} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {2, 9, 11, 12, 13} ∨
        polygon = {2, 5, 11, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 11, 13} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 4, 11, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 11, 13} ∨
        polygon = {2, 4, 9, 11, 12} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 11, 13} ∨
        polygon = {2, 4, 5, 11, 12} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 11} ∨
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
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 11, 13} ∨
        polygon = {2, 3, 4, 11, 12} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 11} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 11} ∨
        polygon = {2, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 9, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14908] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29244 :
    (({2, 3, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {2, 9, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29244 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29244] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29756 :
    (({2, 3, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {2, 10, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29756 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 5, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 12} ∨
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
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29756] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05852 :
    (({2, 3, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {2, 7, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {2, 4, 9, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05852 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
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
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05852] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09948 :
    (({2, 3, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {2, 7, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}, {2, 4, 9, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09948 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
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
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09948] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18140 :
    (({2, 3, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {2, 7, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 10}, {2, 4, 9, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 10}, {2, 4, 6, 10, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18140 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18140] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13020 :
    (({2, 3, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {3, 7, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {2, 7, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}, {2, 4, 9, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13020 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {2, 3, 4, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({2, 3, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13020] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
