module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 097. -/

theorem fin15Anchored_fiveFamily_mask26166 :
    (({1, 2, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {1, 9, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26166 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 13} ∨
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
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26166] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29238 :
    (({1, 2, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {1, 9, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29238 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 13} ∨
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
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29238] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29750 :
    (({1, 2, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {1, 10, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 10, 12, 14}, {1, 5, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29750 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 13} ∨
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
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29750] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05846 :
    (({1, 2, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {2, 4, 9, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05846 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
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
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05846] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09942 :
    (({1, 2, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}, {2, 4, 9, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09942 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 10} ∨
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
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09942] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18134 :
    (({1, 2, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 10}, {2, 4, 9, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 10}, {2, 4, 6, 10, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18134 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 10} ∨
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
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18134] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13014 :
    (({1, 2, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}, {2, 4, 9, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13014 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 12} ∨
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
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13014] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21206 :
    (({1, 2, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 12}, {2, 4, 9, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 12}, {2, 4, 6, 12, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21206 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21206] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25302 :
    (({1, 2, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 13}, {2, 4, 9, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}, {2, 4, 6, 13, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 9}, {1, 7, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25302 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25302] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13526 :
    (({1, 2, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {1, 7, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13526 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13526] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21718 :
    (({1, 2, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 12}, {2, 4, 6, 12, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {1, 7, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21718 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21718] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25814 :
    (({1, 2, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {2, 4, 6, 13, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {1, 7, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25814 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25814] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28886 :
    (({1, 2, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {1, 7, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28886 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28886] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13910 :
    (({1, 2, 4, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 9, 10, 13}, {4, 6, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {1, 9, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 9, 10, 13}, {1, 6, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13910 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13910] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22102 :
    (({1, 2, 4, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 12}, {2, 4, 6, 12, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {1, 9, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22102 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22102] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26198 :
    (({1, 2, 4, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {2, 4, 6, 13, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}, {1, 9, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26198 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26198] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29270 :
    (({1, 2, 4, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {1, 9, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29270 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29270] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29782 :
    (({1, 2, 4, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 10, 12, 14}, {4, 6, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}, {1, 10, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 10, 12, 14}, {1, 6, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29782 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 6, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29782] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13974 :
    (({1, 2, 4, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 7, 9, 12, 13}, {4, 7, 9, 10, 13}, {4, 7, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {1, 9, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 7, 9, 12, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13974 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13974] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22166 :
    (({1, 2, 4, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 12}, {2, 4, 7, 12, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {1, 9, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22166 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22166] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26262 :
    (({1, 2, 4, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {2, 4, 7, 13, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}, {1, 9, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26262 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26262] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29334 :
    (({1, 2, 4, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {1, 9, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29334 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29334] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29846 :
    (({1, 2, 4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 10, 12, 14}, {4, 7, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {1, 10, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29846 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29846] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30230 :
    (({1, 2, 4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 9, 10, 13, 14}, {4, 9, 10, 12, 14}, {4, 9, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {1, 10, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 9, 10, 13, 14}, {1, 9, 10, 12, 14}, {1, 9, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30230 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30230] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05862 :
    (({1, 2, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 6, 9, 10, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {2, 5, 9, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}, {1, 5, 9, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05862 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05862] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09958 :
    (({1, 2, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 6, 9, 10, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}, {2, 5, 9, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}, {1, 5, 9, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 10}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09958 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09958] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18150 :
    (({1, 2, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 6, 9, 10, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 10}, {2, 5, 9, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 10}, {2, 5, 6, 10, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}, {1, 5, 9, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 10}, {1, 5, 6, 10, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18150 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18150] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13030 :
    (({1, 2, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}, {2, 5, 9, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}, {1, 5, 9, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13030 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13030] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21222 :
    (({1, 2, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 12}, {2, 5, 9, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}, {2, 5, 6, 12, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}, {1, 5, 9, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 12}, {1, 5, 6, 12, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21222 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21222] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25318 :
    (({1, 2, 5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {5, 7, 9, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 13}, {2, 5, 9, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 9}, {1, 7, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 13}, {1, 5, 9, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 13}, {1, 5, 6, 13, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 9}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25318 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25318] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13542 :
    (({1, 2, 5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 12}, {2, 5, 10, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {1, 7, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 10, 12}, {1, 5, 10, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13542 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13542] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21734 :
    (({1, 2, 5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 12}, {2, 5, 10, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {1, 7, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 12}, {1, 5, 10, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 12}, {1, 5, 6, 12, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 12}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21734 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21734] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25830 :
    (({1, 2, 5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 13}, {2, 5, 10, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {1, 7, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 13}, {1, 5, 10, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 13}, {1, 5, 6, 13, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25830 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25830] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28902 :
    (({1, 2, 5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {1, 7, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 12, 13}, {1, 5, 12, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 12, 13}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28902 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28902] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13926 :
    (({1, 2, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {1, 9, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 9, 10, 13}, {1, 6, 9, 10, 12}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13926 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13926] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22118 :
    (({1, 2, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 12}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {1, 9, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 12}, {1, 5, 10, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 12}, {1, 5, 6, 12, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22118 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22118] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26214 :
    (({1, 2, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 13}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {1, 9, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 13}, {1, 5, 10, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 13}, {1, 5, 6, 13, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26214 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26214] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29286 :
    (({1, 2, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {1, 9, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 12, 13}, {1, 5, 12, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 12, 13}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29286 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29286] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29798 :
    (({1, 2, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {1, 10, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 10, 12, 14}, {1, 6, 10, 12, 13}, {1, 5, 12, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 10, 12, 14}, {1, 5, 10, 12, 13}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29798 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 6, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29798] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13990 :
    (({1, 2, 5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {1, 9, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 7, 9, 12, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 12}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13990 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 5, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13990] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
