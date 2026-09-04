module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 076. -/

theorem fin15Anchored_fiveFamily_mask29323 :
    (({0, 1, 3, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29323 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29323] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask23691 :
    (({0, 1, 3, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 12, 14}, {3, 10, 11, 12, 14}, {3, 7, 11, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 11, 14}, {3, 7, 10, 11, 12}, {1, 10, 11, 12, 14}, {1, 7, 11, 12, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 11, 14}, {1, 7, 10, 11, 12}, {1, 3, 11, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 11, 14}, {1, 3, 10, 11, 12}, {1, 3, 7, 12, 14}, {1, 3, 7, 11, 14}, {1, 3, 7, 11, 12}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 7, 10, 11}, {0, 10, 11, 12, 14}, {0, 7, 11, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 11, 14}, {0, 7, 10, 11, 12}, {0, 3, 11, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 11, 14}, {0, 3, 10, 11, 12}, {0, 3, 7, 12, 14}, {0, 3, 7, 11, 14}, {0, 3, 7, 11, 12}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 7, 10, 11}, {0, 1, 11, 12, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 11, 14}, {0, 1, 10, 11, 12}, {0, 1, 7, 12, 14}, {0, 1, 7, 11, 14}, {0, 1, 7, 11, 12}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 7, 10, 11}, {0, 1, 3, 12, 14}, {0, 1, 3, 11, 14}, {0, 1, 3, 11, 12}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 10, 11}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 11}, {0, 1, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask23691 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 10, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 11, 12, 14} ∨
        polygon = {3, 10, 11, 12, 14} ∨
        polygon = {3, 7, 11, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 11, 14} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {1, 10, 11, 12, 14} ∨
        polygon = {1, 7, 11, 12, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 10, 11, 14} ∨
        polygon = {1, 7, 10, 11, 12} ∨
        polygon = {1, 3, 11, 12, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 11, 14} ∨
        polygon = {1, 3, 10, 11, 12} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 11, 14} ∨
        polygon = {1, 3, 7, 11, 12} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 10, 11} ∨
        polygon = {0, 10, 11, 12, 14} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 11, 14} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 3, 11, 12, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 11, 14} ∨
        polygon = {0, 3, 10, 11, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 11, 14} ∨
        polygon = {0, 3, 7, 11, 12} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 10, 11} ∨
        polygon = {0, 1, 11, 12, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 11, 14} ∨
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 11, 14} ∨
        polygon = {0, 1, 7, 11, 12} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 11, 14} ∨
        polygon = {0, 1, 3, 11, 12} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 11} ∨
        polygon = {0, 1, 3, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask23691] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29835 :
    (({0, 1, 3, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29835 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29835] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26379 :
    (({0, 1, 3, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 8, 10, 13, 14}, {1, 8, 9, 13, 14}, {1, 8, 9, 10, 14}, {1, 8, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 8, 13, 14}, {1, 3, 8, 10, 14}, {1, 3, 8, 10, 13}, {1, 3, 8, 9, 14}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 10}, {0, 9, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 8, 13, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 8, 13, 14}, {0, 1, 8, 10, 14}, {0, 1, 8, 10, 13}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 13}, {0, 1, 8, 9, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26379 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 8, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 8, 10, 13, 14} ∨
        polygon = {1, 8, 9, 13, 14} ∨
        polygon = {1, 8, 9, 10, 14} ∨
        polygon = {1, 8, 9, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 8, 10, 14} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 8, 10, 14} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26379] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask15883 :
    (({0, 1, 3, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 12, 13}, {3, 10, 11, 12, 13}, {3, 9, 11, 12, 13}, {3, 9, 10, 12, 13}, {3, 9, 10, 11, 13}, {3, 9, 10, 11, 12}, {1, 10, 11, 12, 13}, {1, 9, 11, 12, 13}, {1, 9, 10, 12, 13}, {1, 9, 10, 11, 13}, {1, 9, 10, 11, 12}, {1, 3, 11, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 10, 11, 13}, {1, 3, 10, 11, 12}, {1, 3, 9, 12, 13}, {1, 3, 9, 11, 13}, {1, 3, 9, 11, 12}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 9, 10, 11}, {0, 10, 11, 12, 13}, {0, 9, 11, 12, 13}, {0, 9, 10, 12, 13}, {0, 9, 10, 11, 13}, {0, 9, 10, 11, 12}, {0, 3, 11, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 10, 11, 13}, {0, 3, 10, 11, 12}, {0, 3, 9, 12, 13}, {0, 3, 9, 11, 13}, {0, 3, 9, 11, 12}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 9, 10, 11}, {0, 1, 11, 12, 13}, {0, 1, 10, 12, 13}, {0, 1, 10, 11, 13}, {0, 1, 10, 11, 12}, {0, 1, 9, 12, 13}, {0, 1, 9, 11, 13}, {0, 1, 9, 11, 12}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 9, 10, 11}, {0, 1, 3, 12, 13}, {0, 1, 3, 11, 13}, {0, 1, 3, 11, 12}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 10, 11}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 11}, {0, 1, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask15883 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 9, 10, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {9, 10, 11, 12, 13} ∨
        polygon = {3, 10, 11, 12, 13} ∨
        polygon = {3, 9, 11, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 11, 13} ∨
        polygon = {3, 9, 10, 11, 12} ∨
        polygon = {1, 10, 11, 12, 13} ∨
        polygon = {1, 9, 11, 12, 13} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 9, 10, 11, 13} ∨
        polygon = {1, 9, 10, 11, 12} ∨
        polygon = {1, 3, 11, 12, 13} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 10, 11, 13} ∨
        polygon = {1, 3, 10, 11, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 11, 13} ∨
        polygon = {1, 3, 9, 11, 12} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 9, 10, 11} ∨
        polygon = {0, 10, 11, 12, 13} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 3, 11, 12, 13} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 10, 11, 13} ∨
        polygon = {0, 3, 10, 11, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 9, 11, 12} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 1, 11, 12, 13} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 10, 11, 13} ∨
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 11, 13} ∨
        polygon = {0, 1, 9, 11, 12} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 9, 10, 11} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 11, 13} ∨
        polygon = {0, 1, 3, 11, 12} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 11} ∨
        polygon = {0, 1, 3, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask15883] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30219 :
    (({0, 1, 3, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 9, 10, 13, 14}, {1, 9, 10, 12, 14}, {1, 9, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30219 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30219] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01779 :
    (({0, 1, 4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {4, 6, 7, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 6, 9, 10}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}, {1, 6, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {0, 6, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 1, 7, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01779 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01779] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04851 :
    (({0, 1, 4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {4, 6, 7, 9, 12}, {4, 5, 7, 9, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 9}, {1, 6, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {0, 6, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 1, 7, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04851 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04851] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08947 :
    (({0, 1, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {4, 6, 7, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 9}, {1, 6, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {0, 6, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 1, 7, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08947 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08947] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17139 :
    (({0, 1, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {4, 6, 7, 9, 14}, {4, 5, 7, 9, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 9}, {1, 6, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {0, 6, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 9}, {0, 4, 7, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 9}, {0, 4, 5, 9, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 1, 7, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 4, 9, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17139 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17139] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05363 :
    (({0, 1, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {4, 6, 7, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {1, 6, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 4, 7, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {0, 6, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 4, 7, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 1, 7, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05363 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05363] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09459 :
    (({0, 1, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {4, 6, 7, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}, {1, 6, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}, {1, 4, 7, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {0, 6, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 4, 7, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 1, 7, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09459 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09459] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17651 :
    (({0, 1, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {4, 6, 7, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 10}, {1, 6, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 10}, {1, 4, 7, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 4, 5, 10, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {0, 6, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 4, 7, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 1, 7, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 4, 10, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17651 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17651] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12531 :
    (({0, 1, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {4, 6, 7, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}, {1, 6, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 4, 7, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}, {0, 6, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 4, 7, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}, {0, 1, 7, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12531 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12531] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20723 :
    (({0, 1, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {4, 6, 7, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}, {1, 6, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}, {1, 4, 7, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}, {0, 6, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 4, 7, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}, {0, 1, 7, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 4, 12, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20723 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20723] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24819 :
    (({0, 1, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {4, 6, 7, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {1, 6, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}, {1, 4, 7, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 7}, {0, 6, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 4, 7, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 7}, {0, 1, 7, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 7}, {0, 1, 4, 13, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24819 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24819] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09075 :
    (({0, 1, 4, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 13}, {4, 6, 8, 9, 13}, {4, 5, 8, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 9}, {1, 6, 8, 9, 13}, {1, 5, 8, 9, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 8, 13}, {1, 5, 6, 8, 9}, {1, 4, 8, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 9}, {1, 4, 5, 9, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 9}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 8}, {0, 6, 8, 9, 13}, {0, 5, 8, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 9}, {0, 4, 8, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}, {0, 4, 5, 9, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 1, 8, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 9}, {0, 1, 5, 9, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 9}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 8}, {0, 1, 4, 9, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09075 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 5, 8, 9, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 8, 13} ∨
        polygon = {1, 5, 6, 8, 9} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 8} ∨
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
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09075] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17267 :
    (({0, 1, 4, 5, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 14}, {4, 6, 8, 9, 14}, {4, 5, 8, 9, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 9}, {1, 6, 8, 9, 14}, {1, 5, 8, 9, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 8, 14}, {1, 5, 6, 8, 9}, {1, 4, 8, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 8, 9}, {1, 4, 5, 9, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 9}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 8}, {0, 6, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 9}, {0, 4, 8, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 9}, {0, 4, 5, 9, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 1, 8, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 9}, {0, 1, 5, 9, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 9}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 8}, {0, 1, 4, 9, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17267 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 8, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {1, 6, 8, 9, 14} ∨
        polygon = {1, 5, 8, 9, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 8, 14} ∨
        polygon = {1, 5, 6, 8, 9} ∨
        polygon = {1, 4, 8, 9, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 8} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17267] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05491 :
    (({0, 1, 4, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 12}, {4, 6, 8, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 10}, {1, 6, 8, 10, 12}, {1, 5, 8, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 8, 12}, {1, 5, 6, 8, 10}, {1, 4, 8, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 8, 12}, {1, 4, 6, 8, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 8, 12}, {1, 4, 5, 8, 10}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 8}, {0, 6, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 4, 8, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 1, 8, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 8}, {0, 1, 4, 10, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 8}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05491 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {1, 6, 8, 10, 12} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 8, 12} ∨
        polygon = {1, 5, 6, 8, 10} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 8, 12} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 8} ∨
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
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05491] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05747 :
    (({0, 1, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {1, 6, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {0, 6, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 1, 9, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05747 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 9} ∨
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
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05747] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09843 :
    (({0, 1, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}, {1, 6, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {0, 6, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 1, 9, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09843 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 9} ∨
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
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09843] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18035 :
    (({0, 1, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 10}, {1, 6, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 10}, {1, 4, 9, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {0, 6, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 1, 9, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18035 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 9} ∨
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
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18035] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12915 :
    (({0, 1, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {1, 6, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 4, 9, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {0, 6, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 1, 9, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12915 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 9} ∨
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
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12915] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21107 :
    (({0, 1, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 12}, {1, 6, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {0, 6, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 4, 9, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 1, 9, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21107 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 9} ∨
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
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21107] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25203 :
    (({0, 1, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {1, 6, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {0, 6, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 4, 9, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 1, 9, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25203 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 9} ∨
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
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25203] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13427 :
    (({0, 1, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {1, 6, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {0, 6, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 1, 10, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13427 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 10} ∨
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
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13427] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21619 :
    (({0, 1, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}, {1, 6, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {0, 6, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 1, 10, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21619 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 10} ∨
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
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21619] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25715 :
    (({0, 1, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {1, 6, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {0, 6, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 1, 10, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25715 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 10} ∨
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
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25715] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28787 :
    (({0, 1, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}, {1, 6, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {0, 6, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 1, 12, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28787 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 12} ∨
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
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28787] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01971 :
    (({0, 1, 4, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 10}, {4, 7, 8, 9, 10}, {4, 5, 8, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 7, 8, 10}, {4, 5, 7, 8, 9}, {1, 7, 8, 9, 10}, {1, 5, 8, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 7, 8, 10}, {1, 5, 7, 8, 9}, {1, 4, 8, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 7, 8, 10}, {1, 4, 7, 8, 9}, {1, 4, 5, 9, 10}, {1, 4, 5, 8, 10}, {1, 4, 5, 8, 9}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 4, 5, 7, 8}, {0, 7, 8, 9, 10}, {0, 5, 8, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 4, 8, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 1, 8, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}, {0, 1, 5, 9, 10}, {0, 1, 5, 8, 10}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01971 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 10} ∨
        polygon = {1, 5, 8, 9, 10} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 7, 8} ∨
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
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01971] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17331 :
    (({0, 1, 4, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 14}, {4, 7, 8, 9, 14}, {4, 5, 8, 9, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 9}, {1, 7, 8, 9, 14}, {1, 5, 8, 9, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 8, 14}, {1, 5, 7, 8, 9}, {1, 4, 8, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 9}, {1, 4, 5, 9, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 9}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 9}, {1, 4, 5, 7, 8}, {0, 7, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 9}, {0, 4, 8, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 9}, {0, 4, 5, 9, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 1, 8, 9, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 9}, {0, 1, 5, 9, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 4, 9, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17331 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 8, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 14} ∨
        polygon = {1, 5, 8, 9, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 8, 14} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 4, 8, 9, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 7, 8} ∨
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
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17331] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05555 :
    (({0, 1, 4, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 12}, {4, 7, 8, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 10}, {1, 7, 8, 10, 12}, {1, 5, 8, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 8, 12}, {1, 5, 7, 8, 10}, {1, 4, 8, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 8, 12}, {1, 4, 7, 8, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 8, 12}, {1, 4, 5, 8, 10}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 8}, {0, 7, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 4, 8, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 1, 8, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 8}, {0, 1, 4, 10, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05555 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 12} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 8, 12} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 8, 12} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 8} ∨
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
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05555] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09651 :
    (({0, 1, 4, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 13}, {4, 7, 8, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 10}, {1, 7, 8, 10, 13}, {1, 5, 8, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 8, 13}, {1, 5, 7, 8, 10}, {1, 4, 8, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 8, 13}, {1, 4, 7, 8, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 10}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 8}, {0, 7, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 4, 8, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 1, 8, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 10}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 8}, {0, 1, 4, 10, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09651 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 13} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 8, 13} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 8} ∨
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
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09651] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17843 :
    (({0, 1, 4, 5, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 14}, {4, 7, 8, 10, 14}, {4, 5, 8, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 10}, {1, 7, 8, 10, 14}, {1, 5, 8, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 8, 14}, {1, 5, 7, 8, 10}, {1, 4, 8, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 10}, {1, 4, 5, 10, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 10}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 8}, {0, 7, 8, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 10}, {0, 4, 8, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 1, 8, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 10}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 8}, {0, 1, 4, 10, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17843 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 8, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {4, 7, 8, 10, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 14} ∨
        polygon = {1, 5, 8, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 8, 14} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 4, 8, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 8} ∨
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
        polygon = {0, 1, 8, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17843] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25011 :
    (({0, 1, 4, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 13, 14}, {4, 7, 8, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 13}, {1, 7, 8, 13, 14}, {1, 5, 8, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 8, 14}, {1, 5, 7, 8, 13}, {1, 4, 8, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 8}, {0, 7, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 4, 8, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 8}, {0, 1, 8, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 8}, {0, 1, 4, 13, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 8}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 8}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25011 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {4, 7, 8, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {1, 7, 8, 13, 14} ∨
        polygon = {1, 5, 8, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 8, 14} ∨
        polygon = {1, 5, 7, 8, 13} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 8} ∨
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
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 8} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25011] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05811 :
    (({0, 1, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 9, 10}, {1, 7, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {0, 7, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05811 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 9} ∨
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
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05811] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09907 :
    (({0, 1, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 10}, {1, 7, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {0, 7, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09907 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 9} ∨
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
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09907] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18099 :
    (({0, 1, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 10}, {1, 7, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 10}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {0, 7, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18099 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
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
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18099] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask19123 :
    (({0, 1, 4, 5, 7, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 11, 14}, {4, 7, 9, 11, 14}, {4, 5, 9, 11, 14}, {4, 5, 7, 11, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 11}, {1, 7, 9, 11, 14}, {1, 5, 9, 11, 14}, {1, 5, 7, 11, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 11}, {1, 4, 9, 11, 14}, {1, 4, 7, 11, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 11}, {1, 4, 5, 11, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 11}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 11}, {1, 4, 5, 7, 9}, {0, 7, 9, 11, 14}, {0, 5, 9, 11, 14}, {0, 5, 7, 11, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 11}, {0, 4, 9, 11, 14}, {0, 4, 7, 11, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 11}, {0, 4, 5, 11, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 11}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 11}, {0, 4, 5, 7, 9}, {0, 1, 9, 11, 14}, {0, 1, 7, 11, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 11}, {0, 1, 5, 11, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 11}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 11}, {0, 1, 5, 7, 9}, {0, 1, 4, 11, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 11}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 11}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 11}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask19123 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 9, 11, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 11, 14} ∨
        polygon = {4, 7, 9, 11, 14} ∨
        polygon = {4, 5, 9, 11, 14} ∨
        polygon = {4, 5, 7, 11, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 11} ∨
        polygon = {1, 7, 9, 11, 14} ∨
        polygon = {1, 5, 9, 11, 14} ∨
        polygon = {1, 5, 7, 11, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 11} ∨
        polygon = {1, 4, 9, 11, 14} ∨
        polygon = {1, 4, 7, 11, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 11} ∨
        polygon = {1, 4, 5, 11, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 11} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 11} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {0, 7, 9, 11, 14} ∨
        polygon = {0, 5, 9, 11, 14} ∨
        polygon = {0, 5, 7, 11, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 11} ∨
        polygon = {0, 4, 9, 11, 14} ∨
        polygon = {0, 4, 7, 11, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 11} ∨
        polygon = {0, 4, 5, 11, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 11} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 11} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 1, 9, 11, 14} ∨
        polygon = {0, 1, 7, 11, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 11} ∨
        polygon = {0, 1, 5, 11, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 11} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 11} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 11, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 11} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 11} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask19123] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12979 :
    (({0, 1, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 12}, {1, 7, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {0, 7, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12979 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
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
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12979] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
