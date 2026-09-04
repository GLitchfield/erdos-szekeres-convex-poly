module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 069. -/

theorem fin15Anchored_fiveFamily_mask12503 :
    (({0, 1, 2, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 13}, {2, 6, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {1, 6, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 2, 7, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}, {0, 6, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 2, 7, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}, {0, 1, 7, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12503 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 12} ∨
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
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12503] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20695 :
    (({0, 1, 2, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 14}, {2, 6, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 12}, {1, 6, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 2, 7, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}, {0, 6, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 2, 7, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}, {0, 1, 7, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 2, 12, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20695 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 12} ∨
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
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20695] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24791 :
    (({0, 1, 2, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 13, 14}, {2, 6, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}, {1, 6, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 2, 7, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 7}, {0, 6, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 2, 7, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 7}, {0, 1, 7, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 7}, {0, 1, 2, 13, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24791 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 13} ∨
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
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24791] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05719 :
    (({0, 1, 2, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {1, 6, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {0, 6, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 1, 9, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05719 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
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
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05719] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09815 :
    (({0, 1, 2, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}, {1, 6, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {0, 6, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 1, 9, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09815 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 10} ∨
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
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09815] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18007 :
    (({0, 1, 2, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 10}, {1, 6, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}, {1, 2, 9, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {0, 6, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 2, 9, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 1, 9, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18007 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 10} ∨
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
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18007] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12887 :
    (({0, 1, 2, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {1, 6, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 2, 9, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {0, 6, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 2, 9, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 1, 9, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12887 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 12} ∨
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
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12887] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21079 :
    (({0, 1, 2, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 12}, {1, 6, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 2, 9, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {0, 6, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 2, 9, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 1, 9, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21079 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 12} ∨
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
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21079] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25175 :
    (({0, 1, 2, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}, {1, 6, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 2, 9, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {0, 6, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 2, 9, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}, {0, 1, 9, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25175 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25175] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13399 :
    (({0, 1, 2, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}, {1, 6, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {0, 6, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 1, 10, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13399 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13399] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21591 :
    (({0, 1, 2, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 12}, {1, 6, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {0, 6, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 1, 10, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21591 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21591] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25687 :
    (({0, 1, 2, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}, {1, 6, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {0, 6, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 1, 10, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25687 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25687] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28759 :
    (({0, 1, 2, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}, {1, 6, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {0, 6, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 1, 12, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28759 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28759] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05783 :
    (({0, 1, 2, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 12}, {2, 7, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {1, 7, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {0, 7, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05783 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
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
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05783] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09879 :
    (({0, 1, 2, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 13}, {2, 7, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}, {1, 7, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {0, 7, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09879 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 10} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09879] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18071 :
    (({0, 1, 2, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 14}, {2, 7, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 10}, {1, 7, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {0, 7, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 2, 9, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18071 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 10} ∨
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
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18071] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12951 :
    (({0, 1, 2, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 13}, {2, 7, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {1, 7, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {0, 7, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 2, 9, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12951 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 12} ∨
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
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12951] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21143 :
    (({0, 1, 2, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 14}, {2, 7, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 12}, {1, 7, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {0, 7, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 2, 9, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21143 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 12} ∨
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
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21143] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25239 :
    (({0, 1, 2, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 13, 14}, {2, 7, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}, {1, 7, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {0, 7, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 2, 9, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25239 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 13} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25239] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13463 :
    (({0, 1, 2, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {1, 7, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {0, 7, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13463 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13463] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21655 :
    (({0, 1, 2, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 12}, {1, 7, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {0, 7, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21655 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21655] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25751 :
    (({0, 1, 2, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {1, 7, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {0, 7, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25751 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 13} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25751] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28823 :
    (({0, 1, 2, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {1, 7, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {0, 7, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28823 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28823] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13847 :
    (({0, 1, 2, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {0, 9, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13847 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13847] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22039 :
    (({0, 1, 2, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {0, 9, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22039 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22039] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26135 :
    (({0, 1, 2, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {0, 9, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26135 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 13} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26135] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29207 :
    (({0, 1, 2, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {0, 9, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29207 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29207] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29719 :
    (({0, 1, 2, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {0, 10, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29719 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29719] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01767 :
    (({0, 1, 2, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {2, 6, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {1, 6, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 2, 7, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {0, 6, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 2, 7, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 1, 7, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01767 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01767] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04839 :
    (({0, 1, 2, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {2, 6, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}, {1, 6, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 2, 7, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {0, 6, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 2, 7, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 1, 7, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04839 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04839] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08935 :
    (({0, 1, 2, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {2, 6, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 9}, {1, 6, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 9}, {1, 2, 7, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {0, 6, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 2, 7, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 1, 7, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08935 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08935] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17127 :
    (({0, 1, 2, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {2, 6, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 9}, {1, 6, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 9}, {1, 2, 7, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {0, 6, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 9}, {0, 2, 7, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 9}, {0, 2, 5, 9, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 1, 7, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 2, 9, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17127 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17127] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05351 :
    (({0, 1, 2, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {2, 6, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {1, 6, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 2, 7, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {0, 6, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 2, 7, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 1, 7, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05351 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
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
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05351] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09447 :
    (({0, 1, 2, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {2, 6, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {1, 6, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}, {1, 2, 7, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {0, 6, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 2, 7, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 1, 7, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09447 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
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
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09447] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17639 :
    (({0, 1, 2, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {2, 6, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 10}, {1, 6, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 10}, {1, 2, 7, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 5, 10, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {0, 6, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 2, 7, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 10}, {0, 2, 5, 10, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 1, 7, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 2, 10, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17639 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 10} ∨
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
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17639] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12519 :
    (({0, 1, 2, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {2, 6, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {1, 6, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 2, 7, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}, {0, 6, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 2, 7, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}, {0, 1, 7, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12519 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
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
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12519] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20711 :
    (({0, 1, 2, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {2, 6, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {1, 6, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}, {1, 2, 7, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}, {0, 6, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 2, 7, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 5, 12, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}, {0, 1, 7, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 2, 12, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20711 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
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
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20711] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24807 :
    (({0, 1, 2, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {2, 6, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {1, 6, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}, {1, 2, 7, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 7}, {0, 6, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 2, 7, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 5, 13, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 7}, {0, 1, 7, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 7}, {0, 1, 2, 13, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24807 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
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
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24807] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05735 :
    (({0, 1, 2, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {1, 6, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {0, 6, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 1, 9, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05735 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
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
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05735] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09831 :
    (({0, 1, 2, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {1, 6, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {0, 6, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 1, 9, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09831 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 5, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
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
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09831] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
