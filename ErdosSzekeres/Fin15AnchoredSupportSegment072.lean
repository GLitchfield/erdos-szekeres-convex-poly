module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 072. -/

theorem fin15Anchored_fiveFamily_mask04923 :
    (({0, 1, 3, 4, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 12}, {3, 5, 8, 9, 12}, {3, 4, 8, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 9}, {1, 5, 8, 9, 12}, {1, 4, 8, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 8, 12}, {1, 4, 5, 8, 9}, {1, 3, 8, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 9}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 8}, {0, 5, 8, 9, 12}, {0, 4, 8, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 3, 8, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 1, 8, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 9}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 3, 9, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 9}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04923 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {1, 5, 8, 9, 12} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04923] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09019 :
    (({0, 1, 3, 4, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 13}, {3, 5, 8, 9, 13}, {3, 4, 8, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 9}, {1, 5, 8, 9, 13}, {1, 4, 8, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 9}, {1, 3, 8, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 9}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 8}, {0, 5, 8, 9, 13}, {0, 4, 8, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 9}, {0, 3, 8, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 1, 8, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09019 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {1, 5, 8, 9, 13} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09019] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17211 :
    (({0, 1, 3, 4, 5, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 14}, {3, 5, 8, 9, 14}, {3, 4, 8, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 9}, {1, 5, 8, 9, 14}, {1, 4, 8, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 9}, {1, 3, 8, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 9}, {1, 3, 4, 9, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 9}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 8}, {0, 5, 8, 9, 14}, {0, 4, 8, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 9}, {0, 3, 8, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 9}, {0, 3, 4, 9, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}, {0, 1, 8, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 9}, {0, 1, 4, 9, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 3, 9, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 9}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17211 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {1, 5, 8, 9, 14} ∨
        polygon = {1, 4, 8, 9, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17211] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05435 :
    (({0, 1, 3, 4, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 12}, {3, 5, 8, 10, 12}, {3, 4, 8, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 10}, {1, 5, 8, 10, 12}, {1, 4, 8, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 8, 12}, {1, 4, 5, 8, 10}, {1, 3, 8, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 10}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 8}, {0, 5, 8, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 3, 8, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 1, 8, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 3, 10, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05435 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05435] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09531 :
    (({0, 1, 3, 4, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 10}, {1, 5, 8, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 10}, {1, 3, 8, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 8}, {0, 5, 8, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 3, 8, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 1, 8, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 3, 10, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09531 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09531] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17723 :
    (({0, 1, 3, 4, 5, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 14}, {3, 5, 8, 10, 14}, {3, 4, 8, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 10}, {1, 5, 8, 10, 14}, {1, 4, 8, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 10}, {1, 3, 8, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 8}, {0, 5, 8, 10, 14}, {0, 4, 8, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 3, 8, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 1, 8, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 3, 10, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17723 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 4, 8, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {1, 5, 8, 10, 14} ∨
        polygon = {1, 4, 8, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 3, 8, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17723] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12603 :
    (({0, 1, 3, 4, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 12, 13}, {3, 5, 8, 12, 13}, {3, 4, 8, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 12}, {1, 5, 8, 12, 13}, {1, 4, 8, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 12}, {1, 3, 8, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 8}, {0, 5, 8, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 3, 8, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}, {0, 1, 8, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 8}, {0, 1, 3, 12, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12603 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {1, 5, 8, 12, 13} ∨
        polygon = {1, 4, 8, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 3, 8, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12603] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20795 :
    (({0, 1, 3, 4, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 12, 14}, {3, 5, 8, 12, 14}, {3, 4, 8, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 12}, {1, 5, 8, 12, 14}, {1, 4, 8, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 12}, {1, 3, 8, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 8}, {0, 5, 8, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 12}, {0, 3, 8, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}, {0, 1, 8, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 8}, {0, 1, 3, 12, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20795 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 4, 8, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {1, 5, 8, 12, 14} ∨
        polygon = {1, 4, 8, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 3, 8, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 4, 8, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20795] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24891 :
    (({0, 1, 3, 4, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 13, 14}, {3, 5, 8, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 13}, {1, 5, 8, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 13}, {1, 3, 8, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 8}, {0, 5, 8, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 3, 8, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}, {0, 1, 8, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 8}, {0, 1, 3, 13, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 8}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24891 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {1, 5, 8, 13, 14} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 8} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24891] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05691 :
    (({0, 1, 3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {1, 5, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {0, 5, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 1, 9, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05691 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05691] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09787 :
    (({0, 1, 3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {1, 5, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {0, 5, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 1, 9, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09787 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09787] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17979 :
    (({0, 1, 3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {1, 5, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {0, 5, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 1, 9, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17979 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17979] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12859 :
    (({0, 1, 3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {1, 5, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {0, 5, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 1, 9, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12859 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12859] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21051 :
    (({0, 1, 3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {1, 5, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {0, 5, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 1, 9, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21051 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21051] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25147 :
    (({0, 1, 3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {1, 5, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {0, 5, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 1, 9, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25147 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25147] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask07227 :
    (({0, 1, 3, 4, 5, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 11, 12}, {3, 5, 10, 11, 12}, {3, 4, 10, 11, 12}, {3, 4, 5, 11, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 10, 11}, {1, 5, 10, 11, 12}, {1, 4, 10, 11, 12}, {1, 4, 5, 11, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 10, 11}, {1, 3, 10, 11, 12}, {1, 3, 5, 11, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 10, 11}, {1, 3, 4, 11, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 10, 11}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 11}, {1, 3, 4, 5, 10}, {0, 5, 10, 11, 12}, {0, 4, 10, 11, 12}, {0, 4, 5, 11, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 10, 11}, {0, 3, 10, 11, 12}, {0, 3, 5, 11, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 10, 11}, {0, 3, 4, 11, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 10, 11}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 11}, {0, 3, 4, 5, 10}, {0, 1, 10, 11, 12}, {0, 1, 5, 11, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 10, 11}, {0, 1, 4, 11, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 10, 11}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 11}, {0, 1, 4, 5, 10}, {0, 1, 3, 11, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 10, 11}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 11}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 11}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07227 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 10, 11} ∨
        polygon = {1, 5, 10, 11, 12} ∨
        polygon = {1, 4, 10, 11, 12} ∨
        polygon = {1, 4, 5, 11, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 10, 11} ∨
        polygon = {1, 3, 10, 11, 12} ∨
        polygon = {1, 3, 5, 11, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 10, 11} ∨
        polygon = {1, 3, 4, 11, 12} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 10, 11} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 11} ∨
        polygon = {1, 3, 4, 5, 10} ∨
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
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 5, 11, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 10, 11} ∨
        polygon = {0, 1, 4, 11, 12} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 11} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 3, 11, 12} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 11} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 11} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07227] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13371 :
    (({0, 1, 3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {1, 5, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {0, 5, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 1, 10, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13371 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13371] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21563 :
    (({0, 1, 3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {1, 5, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {0, 5, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 1, 10, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21563 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21563] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25659 :
    (({0, 1, 3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {1, 5, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {0, 5, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 1, 10, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25659 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25659] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28731 :
    (({0, 1, 3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {1, 5, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {0, 5, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 1, 12, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28731 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 5, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28731] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00987 :
    (({0, 1, 3, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 9}, {3, 6, 7, 8, 9}, {3, 4, 7, 8, 9}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}, {1, 6, 7, 8, 9}, {1, 4, 7, 8, 9}, {1, 4, 6, 8, 9}, {1, 4, 6, 7, 9}, {1, 4, 6, 7, 8}, {1, 3, 7, 8, 9}, {1, 3, 6, 8, 9}, {1, 3, 6, 7, 9}, {1, 3, 6, 7, 8}, {1, 3, 4, 8, 9}, {1, 3, 4, 7, 9}, {1, 3, 4, 7, 8}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 8}, {1, 3, 4, 6, 7}, {0, 6, 7, 8, 9}, {0, 4, 7, 8, 9}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 3, 7, 8, 9}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}, {0, 1, 7, 8, 9}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00987 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00987] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08667 :
    (({0, 1, 3, 4, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 13}, {3, 6, 7, 8, 13}, {3, 4, 7, 8, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 8}, {1, 6, 7, 8, 13}, {1, 4, 7, 8, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 8}, {1, 3, 7, 8, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 8}, {1, 3, 4, 8, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 8}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 8}, {1, 3, 4, 6, 7}, {0, 6, 7, 8, 13}, {0, 4, 7, 8, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 8}, {0, 3, 7, 8, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 8}, {0, 3, 4, 8, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}, {0, 1, 7, 8, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 8}, {0, 1, 4, 8, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}, {0, 1, 3, 8, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08667 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 8, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {1, 6, 7, 8, 13} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08667] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16859 :
    (({0, 1, 3, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 14}, {3, 6, 7, 8, 14}, {3, 4, 7, 8, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 8}, {1, 6, 7, 8, 14}, {1, 4, 7, 8, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 8}, {1, 3, 7, 8, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 8}, {1, 3, 4, 8, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 8}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 8}, {1, 3, 4, 6, 7}, {0, 6, 7, 8, 14}, {0, 4, 7, 8, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 8}, {0, 3, 7, 8, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 8}, {0, 3, 4, 8, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}, {0, 1, 7, 8, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 8}, {0, 1, 4, 8, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}, {0, 1, 3, 8, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16859 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 8, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16859] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01755 :
    (({0, 1, 3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {3, 6, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {1, 6, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {0, 6, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 1, 7, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01755 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01755] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04827 :
    (({0, 1, 3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {3, 6, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {1, 6, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {0, 6, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 1, 7, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04827 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04827] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08923 :
    (({0, 1, 3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {3, 6, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {1, 6, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {0, 6, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 1, 7, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08923 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08923] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17115 :
    (({0, 1, 3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {3, 6, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 9}, {1, 6, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {0, 6, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 9}, {0, 3, 7, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}, {0, 3, 4, 9, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 1, 7, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 3, 9, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17115 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17115] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask03291 :
    (({0, 1, 3, 4, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 11}, {3, 6, 7, 10, 11}, {3, 4, 7, 10, 11}, {3, 4, 6, 10, 11}, {3, 4, 6, 7, 11}, {3, 4, 6, 7, 10}, {1, 6, 7, 10, 11}, {1, 4, 7, 10, 11}, {1, 4, 6, 10, 11}, {1, 4, 6, 7, 11}, {1, 4, 6, 7, 10}, {1, 3, 7, 10, 11}, {1, 3, 6, 10, 11}, {1, 3, 6, 7, 11}, {1, 3, 6, 7, 10}, {1, 3, 4, 10, 11}, {1, 3, 4, 7, 11}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 11}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {0, 6, 7, 10, 11}, {0, 4, 7, 10, 11}, {0, 4, 6, 10, 11}, {0, 4, 6, 7, 11}, {0, 4, 6, 7, 10}, {0, 3, 7, 10, 11}, {0, 3, 6, 10, 11}, {0, 3, 6, 7, 11}, {0, 3, 6, 7, 10}, {0, 3, 4, 10, 11}, {0, 3, 4, 7, 11}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 11}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 1, 7, 10, 11}, {0, 1, 6, 10, 11}, {0, 1, 6, 7, 11}, {0, 1, 6, 7, 10}, {0, 1, 4, 10, 11}, {0, 1, 4, 7, 11}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 11}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 3, 10, 11}, {0, 1, 3, 7, 11}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 11}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 11}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask03291 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {3, 6, 7, 10, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {3, 4, 6, 7, 11} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 11} ∨
        polygon = {1, 4, 7, 10, 11} ∨
        polygon = {1, 4, 6, 10, 11} ∨
        polygon = {1, 4, 6, 7, 11} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 11} ∨
        polygon = {1, 3, 6, 10, 11} ∨
        polygon = {1, 3, 6, 7, 11} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 10, 11} ∨
        polygon = {1, 3, 4, 7, 11} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 11} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {0, 6, 7, 10, 11} ∨
        polygon = {0, 4, 7, 10, 11} ∨
        polygon = {0, 4, 6, 10, 11} ∨
        polygon = {0, 4, 6, 7, 11} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 11} ∨
        polygon = {0, 3, 6, 10, 11} ∨
        polygon = {0, 3, 6, 7, 11} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 10, 11} ∨
        polygon = {0, 3, 4, 7, 11} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 11} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 6, 10, 11} ∨
        polygon = {0, 1, 6, 7, 11} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 11} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 7, 11} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 11} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 11} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask03291] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05339 :
    (({0, 1, 3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {3, 6, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {1, 6, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 3, 7, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {0, 6, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 3, 7, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 1, 7, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05339 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05339] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09435 :
    (({0, 1, 3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {3, 6, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {1, 6, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 3, 7, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {0, 6, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 3, 7, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 1, 7, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09435 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09435] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17627 :
    (({0, 1, 3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {3, 6, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {1, 6, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 3, 7, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {0, 6, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 3, 7, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 1, 7, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 3, 10, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17627 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17627] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12507 :
    (({0, 1, 3, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 13}, {3, 6, 7, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {1, 6, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 3, 7, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 7}, {0, 6, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 3, 7, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 1, 7, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12507 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12507] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20699 :
    (({0, 1, 3, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 14}, {3, 6, 7, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {1, 6, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 3, 7, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 7}, {0, 6, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 3, 7, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 1, 7, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 3, 12, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20699 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20699] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24795 :
    (({0, 1, 3, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 13, 14}, {3, 6, 7, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {1, 6, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 3, 7, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 7}, {0, 6, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 3, 7, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 7}, {0, 1, 7, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 7}, {0, 1, 3, 13, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24795 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24795] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04955 :
    (({0, 1, 3, 4, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 12}, {3, 6, 8, 9, 12}, {3, 4, 8, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 9}, {1, 6, 8, 9, 12}, {1, 4, 8, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 8, 12}, {1, 4, 6, 8, 9}, {1, 3, 8, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 9}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 8}, {0, 6, 8, 9, 12}, {0, 4, 8, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 3, 8, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}, {0, 1, 8, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}, {0, 1, 3, 9, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 9}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04955 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {1, 6, 8, 9, 12} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 8, 12} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 8, 12} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04955] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09563 :
    (({0, 1, 3, 4, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 10, 13}, {3, 6, 8, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 10}, {1, 6, 8, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 10}, {1, 3, 8, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 10}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 8}, {0, 6, 8, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 3, 8, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 1, 8, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 8}, {0, 1, 3, 10, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09563 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {1, 6, 8, 10, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 8, 13} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09563] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05723 :
    (({0, 1, 3, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {1, 6, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {0, 6, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 1, 9, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05723 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
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
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05723] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09819 :
    (({0, 1, 3, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {1, 6, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {0, 6, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 1, 9, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09819 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09819] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18011 :
    (({0, 1, 3, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {1, 6, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {0, 6, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 1, 9, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18011 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
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
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18011] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12891 :
    (({0, 1, 3, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {1, 6, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {0, 6, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 1, 9, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12891 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
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
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12891] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
