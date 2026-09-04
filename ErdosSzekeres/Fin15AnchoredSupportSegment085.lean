module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 085. -/

theorem fin15Anchored_fiveFamily_mask29845 :
    (({0, 2, 4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 10, 12, 14}, {4, 7, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29845 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 4, 7, 10, 12, 13, 14} →
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
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29845] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30229 :
    (({0, 2, 4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 9, 10, 13, 14}, {4, 9, 10, 12, 14}, {4, 9, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 10, 12, 14}, {2, 4, 10, 12, 13}, {2, 4, 9, 13, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30229 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 4, 9, 10, 12, 13, 14} →
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
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30229] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05861 :
    (({0, 2, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 6, 9, 10, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {2, 5, 9, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {0, 7, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 5, 9, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 2, 9, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05861 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 9, 10, 12} →
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
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05861] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09957 :
    (({0, 2, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 6, 9, 10, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}, {2, 5, 9, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {0, 7, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 5, 9, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 2, 9, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09957 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 9, 10, 13} →
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
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
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
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09957] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18149 :
    (({0, 2, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 6, 9, 10, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 10}, {2, 5, 9, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 10}, {2, 5, 6, 10, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {0, 7, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}, {0, 5, 9, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 2, 9, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 10}, {0, 2, 6, 10, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 5, 10, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18149 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 9, 10, 14} →
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
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18149] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13029 :
    (({0, 2, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}, {2, 5, 9, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}, {0, 7, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 5, 9, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 2, 9, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13029 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 9, 12, 13} →
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
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13029] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21221 :
    (({0, 2, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 12}, {2, 5, 9, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}, {2, 5, 6, 12, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}, {0, 7, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 5, 9, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 2, 9, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 6, 12, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}, {0, 2, 5, 12, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21221 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 9, 12, 14} →
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
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21221] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25317 :
    (({0, 2, 5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {5, 7, 9, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 13}, {2, 5, 9, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 9}, {0, 7, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 5, 9, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 2, 9, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 6, 13, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 9}, {0, 2, 5, 13, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25317 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 9, 13, 14} →
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
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25317] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13541 :
    (({0, 2, 5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 7, 12, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 12}, {2, 5, 10, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {0, 7, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 2, 10, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13541 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 10, 12, 13} →
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
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13541] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21733 :
    (({0, 2, 5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 12}, {2, 5, 10, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {0, 7, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 2, 10, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21733 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 10, 12, 14} →
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
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21733] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25829 :
    (({0, 2, 5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 13}, {2, 5, 10, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {0, 7, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 2, 10, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25829 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 10, 13, 14} →
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
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25829] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28901 :
    (({0, 2, 5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 7, 13, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {0, 7, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 2, 12, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28901 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 7, 12, 13, 14} →
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
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28901] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13925 :
    (({0, 2, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {0, 9, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13925 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 9, 10, 12, 13} →
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
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13925] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22117 :
    (({0, 2, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 12}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {0, 9, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22117 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 9, 10, 12, 14} →
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
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22117] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26213 :
    (({0, 2, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 13}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {0, 9, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26213 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 9, 10, 13, 14} →
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
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26213] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29285 :
    (({0, 2, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {0, 9, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29285 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 9, 12, 13, 14} →
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
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29285] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask23653 :
    (({0, 2, 5, 6, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 11, 12, 14}, {5, 10, 11, 12, 14}, {5, 6, 11, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 11, 14}, {5, 6, 10, 11, 12}, {2, 10, 11, 12, 14}, {2, 6, 11, 12, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 11, 14}, {2, 6, 10, 11, 12}, {2, 5, 11, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 11, 14}, {2, 5, 10, 11, 12}, {2, 5, 6, 12, 14}, {2, 5, 6, 11, 14}, {2, 5, 6, 11, 12}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 5, 6, 10, 11}, {0, 10, 11, 12, 14}, {0, 6, 11, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 11, 14}, {0, 6, 10, 11, 12}, {0, 5, 11, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 11, 14}, {0, 5, 10, 11, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 11, 14}, {0, 5, 6, 11, 12}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 10, 11}, {0, 2, 11, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 11, 14}, {0, 2, 10, 11, 12}, {0, 2, 6, 12, 14}, {0, 2, 6, 11, 14}, {0, 2, 6, 11, 12}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 6, 10, 11}, {0, 2, 5, 12, 14}, {0, 2, 5, 11, 14}, {0, 2, 5, 11, 12}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 10, 11}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 11}, {0, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask23653 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 10, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 11, 12, 14} ∨
        polygon = {5, 10, 11, 12, 14} ∨
        polygon = {5, 6, 11, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 11, 14} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {2, 10, 11, 12, 14} ∨
        polygon = {2, 6, 11, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 11, 14} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 5, 11, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 11, 14} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 11, 14} ∨
        polygon = {2, 5, 6, 11, 12} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {0, 10, 11, 12, 14} ∨
        polygon = {0, 6, 11, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 11, 14} ∨
        polygon = {0, 6, 10, 11, 12} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 11, 14} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 11, 14} ∨
        polygon = {0, 5, 6, 11, 12} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 10, 11} ∨
        polygon = {0, 2, 11, 12, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 11, 14} ∨
        polygon = {0, 2, 10, 11, 12} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 11, 14} ∨
        polygon = {0, 2, 6, 11, 12} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 10, 11} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 11, 14} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 11} ∨
        polygon = {0, 2, 5, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask23653] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29797 :
    (({0, 2, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {0, 10, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29797 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 6, 10, 12, 13, 14} →
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
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29797] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13989 :
    (({0, 2, 5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13989 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 7, 9, 10, 12, 13} →
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
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13989] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22181 :
    (({0, 2, 5, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 12}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22181 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22181] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26277 :
    (({0, 2, 5, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 13}, {2, 5, 10, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26277 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26277] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29349 :
    (({0, 2, 5, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29349 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29349] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask23717 :
    (({0, 2, 5, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 12, 14}, {5, 10, 11, 12, 14}, {5, 7, 11, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 11, 14}, {5, 7, 10, 11, 12}, {2, 10, 11, 12, 14}, {2, 7, 11, 12, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 11, 14}, {2, 7, 10, 11, 12}, {2, 5, 11, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 11, 14}, {2, 5, 10, 11, 12}, {2, 5, 7, 12, 14}, {2, 5, 7, 11, 14}, {2, 5, 7, 11, 12}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 5, 7, 10, 11}, {0, 10, 11, 12, 14}, {0, 7, 11, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 11, 14}, {0, 7, 10, 11, 12}, {0, 5, 11, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 11, 14}, {0, 5, 10, 11, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 11, 14}, {0, 5, 7, 11, 12}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 10, 11}, {0, 2, 11, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 11, 14}, {0, 2, 10, 11, 12}, {0, 2, 7, 12, 14}, {0, 2, 7, 11, 14}, {0, 2, 7, 11, 12}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 7, 10, 11}, {0, 2, 5, 12, 14}, {0, 2, 5, 11, 14}, {0, 2, 5, 11, 12}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 5, 10, 11}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 11}, {0, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask23717 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 7, 10, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 11, 12, 14} ∨
        polygon = {5, 10, 11, 12, 14} ∨
        polygon = {5, 7, 11, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 11, 14} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {2, 10, 11, 12, 14} ∨
        polygon = {2, 7, 11, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 11, 14} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {2, 5, 11, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 11, 14} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 11, 14} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {0, 10, 11, 12, 14} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 11, 14} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 11, 14} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 11, 14} ∨
        polygon = {0, 5, 7, 11, 12} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 11} ∨
        polygon = {0, 2, 11, 12, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 11, 14} ∨
        polygon = {0, 2, 10, 11, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 11, 14} ∨
        polygon = {0, 2, 7, 11, 12} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 10, 11} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 11, 14} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 11} ∨
        polygon = {0, 2, 5, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask23717] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29861 :
    (({0, 2, 5, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29861 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29861] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30885 :
    (({0, 2, 5, 7, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 11, 12, 13, 14}, {5, 11, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 11, 13, 14}, {5, 7, 11, 12, 14}, {5, 7, 11, 12, 13}, {2, 11, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 11, 13, 14}, {2, 7, 11, 12, 14}, {2, 7, 11, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 11, 13, 14}, {2, 5, 11, 12, 14}, {2, 5, 11, 12, 13}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 5, 7, 11, 14}, {2, 5, 7, 11, 13}, {2, 5, 7, 11, 12}, {0, 11, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 11, 13, 14}, {0, 7, 11, 12, 14}, {0, 7, 11, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 11, 13, 14}, {0, 5, 11, 12, 14}, {0, 5, 11, 12, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 11, 14}, {0, 5, 7, 11, 13}, {0, 5, 7, 11, 12}, {0, 2, 12, 13, 14}, {0, 2, 11, 13, 14}, {0, 2, 11, 12, 14}, {0, 2, 11, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 11, 14}, {0, 2, 7, 11, 13}, {0, 2, 7, 11, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 11, 14}, {0, 2, 5, 11, 13}, {0, 2, 5, 11, 12}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30885 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 7, 11, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 11, 12, 13, 14} ∨
        polygon = {5, 11, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 11, 13, 14} ∨
        polygon = {5, 7, 11, 12, 14} ∨
        polygon = {5, 7, 11, 12, 13} ∨
        polygon = {2, 11, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 11, 13, 14} ∨
        polygon = {2, 7, 11, 12, 14} ∨
        polygon = {2, 7, 11, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 11, 13, 14} ∨
        polygon = {2, 5, 11, 12, 14} ∨
        polygon = {2, 5, 11, 12, 13} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 11, 14} ∨
        polygon = {2, 5, 7, 11, 13} ∨
        polygon = {2, 5, 7, 11, 12} ∨
        polygon = {0, 11, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 11, 13, 14} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 7, 11, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 11, 13, 14} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 11, 12, 13} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 11, 14} ∨
        polygon = {0, 5, 7, 11, 13} ∨
        polygon = {0, 5, 7, 11, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 11, 13, 14} ∨
        polygon = {0, 2, 11, 12, 14} ∨
        polygon = {0, 2, 11, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 11, 14} ∨
        polygon = {0, 2, 7, 11, 13} ∨
        polygon = {0, 2, 7, 11, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 11, 14} ∨
        polygon = {0, 2, 5, 11, 13} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 11} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 7, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30885] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask15909 :
    (({0, 2, 5, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 12, 13}, {5, 10, 11, 12, 13}, {5, 9, 11, 12, 13}, {5, 9, 10, 12, 13}, {5, 9, 10, 11, 13}, {5, 9, 10, 11, 12}, {2, 10, 11, 12, 13}, {2, 9, 11, 12, 13}, {2, 9, 10, 12, 13}, {2, 9, 10, 11, 13}, {2, 9, 10, 11, 12}, {2, 5, 11, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 10, 11, 13}, {2, 5, 10, 11, 12}, {2, 5, 9, 12, 13}, {2, 5, 9, 11, 13}, {2, 5, 9, 11, 12}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 5, 9, 10, 11}, {0, 10, 11, 12, 13}, {0, 9, 11, 12, 13}, {0, 9, 10, 12, 13}, {0, 9, 10, 11, 13}, {0, 9, 10, 11, 12}, {0, 5, 11, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 10, 11, 13}, {0, 5, 10, 11, 12}, {0, 5, 9, 12, 13}, {0, 5, 9, 11, 13}, {0, 5, 9, 11, 12}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 9, 10, 11}, {0, 2, 11, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 10, 11, 13}, {0, 2, 10, 11, 12}, {0, 2, 9, 12, 13}, {0, 2, 9, 11, 13}, {0, 2, 9, 11, 12}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 9, 10, 11}, {0, 2, 5, 12, 13}, {0, 2, 5, 11, 13}, {0, 2, 5, 11, 12}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 10, 11}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 11}, {0, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask15909 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 9, 10, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {9, 10, 11, 12, 13} ∨
        polygon = {5, 10, 11, 12, 13} ∨
        polygon = {5, 9, 11, 12, 13} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 11, 13} ∨
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {2, 10, 11, 12, 13} ∨
        polygon = {2, 9, 11, 12, 13} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 9, 10, 11, 13} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {2, 5, 11, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 10, 11, 13} ∨
        polygon = {2, 5, 10, 11, 12} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 11, 13} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {0, 10, 11, 12, 13} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 5, 11, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 10, 11, 13} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 11, 13} ∨
        polygon = {0, 5, 9, 11, 12} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 11} ∨
        polygon = {0, 2, 11, 12, 13} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 10, 11, 13} ∨
        polygon = {0, 2, 10, 11, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 9, 10, 11} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 11, 13} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 11} ∨
        polygon = {0, 2, 5, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask15909] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30245 :
    (({0, 2, 5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 10, 12, 14}, {2, 5, 10, 12, 13}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30245 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30245] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask31269 :
    (({0, 2, 5, 9, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 11, 12, 13, 14}, {5, 11, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 11, 13, 14}, {5, 9, 11, 12, 14}, {5, 9, 11, 12, 13}, {2, 11, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 11, 13, 14}, {2, 9, 11, 12, 14}, {2, 9, 11, 12, 13}, {2, 5, 12, 13, 14}, {2, 5, 11, 13, 14}, {2, 5, 11, 12, 14}, {2, 5, 11, 12, 13}, {2, 5, 9, 13, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 12, 13}, {2, 5, 9, 11, 14}, {2, 5, 9, 11, 13}, {2, 5, 9, 11, 12}, {0, 11, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 11, 13, 14}, {0, 9, 11, 12, 14}, {0, 9, 11, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 11, 13, 14}, {0, 5, 11, 12, 14}, {0, 5, 11, 12, 13}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 9, 11, 14}, {0, 5, 9, 11, 13}, {0, 5, 9, 11, 12}, {0, 2, 12, 13, 14}, {0, 2, 11, 13, 14}, {0, 2, 11, 12, 14}, {0, 2, 11, 12, 13}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 9, 11, 14}, {0, 2, 9, 11, 13}, {0, 2, 9, 11, 12}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 5, 11, 14}, {0, 2, 5, 11, 13}, {0, 2, 5, 11, 12}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask31269 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 5, 9, 11, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 11, 12, 13, 14} ∨
        polygon = {5, 11, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 11, 13, 14} ∨
        polygon = {5, 9, 11, 12, 14} ∨
        polygon = {5, 9, 11, 12, 13} ∨
        polygon = {2, 11, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 9, 11, 13, 14} ∨
        polygon = {2, 9, 11, 12, 14} ∨
        polygon = {2, 9, 11, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 5, 11, 13, 14} ∨
        polygon = {2, 5, 11, 12, 14} ∨
        polygon = {2, 5, 11, 12, 13} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 11, 14} ∨
        polygon = {2, 5, 9, 11, 13} ∨
        polygon = {2, 5, 9, 11, 12} ∨
        polygon = {0, 11, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 11, 13, 14} ∨
        polygon = {0, 9, 11, 12, 14} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 11, 13, 14} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 11, 12, 13} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 11, 14} ∨
        polygon = {0, 5, 9, 11, 13} ∨
        polygon = {0, 5, 9, 11, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 11, 13, 14} ∨
        polygon = {0, 2, 11, 12, 14} ∨
        polygon = {0, 2, 11, 12, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 11, 14} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 11, 14} ∨
        polygon = {0, 2, 5, 11, 13} ∨
        polygon = {0, 2, 5, 11, 12} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 11} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 5, 9, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask31269] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14021 :
    (({0, 2, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {2, 6, 10, 12, 13}, {2, 6, 9, 12, 13}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}, {2, 6, 7, 12, 13}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14021 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 6, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14021] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22213 :
    (({0, 2, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 12}, {2, 6, 10, 12, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 12}, {2, 6, 7, 12, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 12}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 12}, {2, 6, 7, 9, 10}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22213 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 6, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22213] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26309 :
    (({0, 2, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 13}, {2, 6, 10, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 13}, {2, 6, 7, 13, 14}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 13}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 10}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26309 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 6, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26309] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29381 :
    (({0, 2, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 12, 13}, {2, 6, 12, 13, 14}, {2, 6, 9, 13, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 12, 13}, {2, 6, 7, 13, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 12, 13}, {2, 6, 7, 9, 14}, {2, 6, 7, 9, 13}, {2, 6, 7, 9, 12}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29381 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 6, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29381] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29893 :
    (({0, 2, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}, {2, 6, 12, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 12, 13}, {2, 6, 7, 13, 14}, {2, 6, 7, 12, 14}, {2, 6, 7, 12, 13}, {2, 6, 7, 10, 14}, {2, 6, 7, 10, 13}, {2, 6, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29893 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 6, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29893] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask15941 :
    (({0, 2, 6, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 12, 13}, {6, 10, 11, 12, 13}, {6, 9, 11, 12, 13}, {6, 9, 10, 12, 13}, {6, 9, 10, 11, 13}, {6, 9, 10, 11, 12}, {2, 10, 11, 12, 13}, {2, 9, 11, 12, 13}, {2, 9, 10, 12, 13}, {2, 9, 10, 11, 13}, {2, 9, 10, 11, 12}, {2, 6, 11, 12, 13}, {2, 6, 10, 12, 13}, {2, 6, 10, 11, 13}, {2, 6, 10, 11, 12}, {2, 6, 9, 12, 13}, {2, 6, 9, 11, 13}, {2, 6, 9, 11, 12}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}, {2, 6, 9, 10, 11}, {0, 10, 11, 12, 13}, {0, 9, 11, 12, 13}, {0, 9, 10, 12, 13}, {0, 9, 10, 11, 13}, {0, 9, 10, 11, 12}, {0, 6, 11, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 10, 11, 13}, {0, 6, 10, 11, 12}, {0, 6, 9, 12, 13}, {0, 6, 9, 11, 13}, {0, 6, 9, 11, 12}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 9, 10, 11}, {0, 2, 11, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 10, 11, 13}, {0, 2, 10, 11, 12}, {0, 2, 9, 12, 13}, {0, 2, 9, 11, 13}, {0, 2, 9, 11, 12}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 9, 10, 11}, {0, 2, 6, 12, 13}, {0, 2, 6, 11, 13}, {0, 2, 6, 11, 12}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 6, 10, 11}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 11}, {0, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask15941 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 6, 9, 10, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {9, 10, 11, 12, 13} ∨
        polygon = {6, 10, 11, 12, 13} ∨
        polygon = {6, 9, 11, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 11, 13} ∨
        polygon = {6, 9, 10, 11, 12} ∨
        polygon = {2, 10, 11, 12, 13} ∨
        polygon = {2, 9, 11, 12, 13} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 9, 10, 11, 13} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {2, 6, 11, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 10, 11, 13} ∨
        polygon = {2, 6, 10, 11, 12} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 11, 13} ∨
        polygon = {2, 6, 9, 11, 12} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {0, 10, 11, 12, 13} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 6, 11, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 10, 11, 13} ∨
        polygon = {0, 6, 10, 11, 12} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 9, 11, 13} ∨
        polygon = {0, 6, 9, 11, 12} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 11} ∨
        polygon = {0, 2, 11, 12, 13} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 10, 11, 13} ∨
        polygon = {0, 2, 10, 11, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 9, 10, 11} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 11, 13} ∨
        polygon = {0, 2, 6, 11, 12} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 10, 11} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 11} ∨
        polygon = {0, 2, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 6, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask15941] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30277 :
    (({0, 2, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}, {2, 6, 12, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 12, 13}, {2, 6, 9, 13, 14}, {2, 6, 9, 12, 14}, {2, 6, 9, 12, 13}, {2, 6, 9, 10, 14}, {2, 6, 9, 10, 13}, {2, 6, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30277 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 6, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30277] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16005 :
    (({0, 2, 7, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 12, 13}, {7, 10, 11, 12, 13}, {7, 9, 11, 12, 13}, {7, 9, 10, 12, 13}, {7, 9, 10, 11, 13}, {7, 9, 10, 11, 12}, {2, 10, 11, 12, 13}, {2, 9, 11, 12, 13}, {2, 9, 10, 12, 13}, {2, 9, 10, 11, 13}, {2, 9, 10, 11, 12}, {2, 7, 11, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 10, 11, 13}, {2, 7, 10, 11, 12}, {2, 7, 9, 12, 13}, {2, 7, 9, 11, 13}, {2, 7, 9, 11, 12}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {2, 7, 9, 10, 11}, {0, 10, 11, 12, 13}, {0, 9, 11, 12, 13}, {0, 9, 10, 12, 13}, {0, 9, 10, 11, 13}, {0, 9, 10, 11, 12}, {0, 7, 11, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 10, 11, 13}, {0, 7, 10, 11, 12}, {0, 7, 9, 12, 13}, {0, 7, 9, 11, 13}, {0, 7, 9, 11, 12}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 7, 9, 10, 11}, {0, 2, 11, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 10, 11, 13}, {0, 2, 10, 11, 12}, {0, 2, 9, 12, 13}, {0, 2, 9, 11, 13}, {0, 2, 9, 11, 12}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 9, 10, 11}, {0, 2, 7, 12, 13}, {0, 2, 7, 11, 13}, {0, 2, 7, 11, 12}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 7, 10, 11}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 11}, {0, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16005 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 7, 9, 10, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {9, 10, 11, 12, 13} ∨
        polygon = {7, 10, 11, 12, 13} ∨
        polygon = {7, 9, 11, 12, 13} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {7, 9, 10, 11, 13} ∨
        polygon = {7, 9, 10, 11, 12} ∨
        polygon = {2, 10, 11, 12, 13} ∨
        polygon = {2, 9, 11, 12, 13} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 9, 10, 11, 13} ∨
        polygon = {2, 9, 10, 11, 12} ∨
        polygon = {2, 7, 11, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 7, 10, 11, 13} ∨
        polygon = {2, 7, 10, 11, 12} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 11, 13} ∨
        polygon = {2, 7, 9, 11, 12} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 11} ∨
        polygon = {0, 10, 11, 12, 13} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 7, 11, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 10, 11, 13} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 9, 11, 13} ∨
        polygon = {0, 7, 9, 11, 12} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 11} ∨
        polygon = {0, 2, 11, 12, 13} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 10, 11, 13} ∨
        polygon = {0, 2, 10, 11, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 11, 13} ∨
        polygon = {0, 2, 9, 11, 12} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 9, 10, 11} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 11, 13} ∨
        polygon = {0, 2, 7, 11, 12} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 10, 11} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 11} ∨
        polygon = {0, 2, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 7, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16005] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30341 :
    (({0, 2, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}, {2, 7, 9, 13, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30341 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 2, 7, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 2, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30341] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01529 :
    (({0, 3, 4, 5, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 8, 10}, {4, 6, 7, 8, 10}, {4, 5, 7, 8, 10}, {4, 5, 6, 8, 10}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 8}, {3, 6, 7, 8, 10}, {3, 5, 7, 8, 10}, {3, 5, 6, 8, 10}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 8}, {3, 4, 7, 8, 10}, {3, 4, 6, 8, 10}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 8}, {3, 4, 5, 8, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 8}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 8}, {3, 4, 5, 6, 7}, {0, 6, 7, 8, 10}, {0, 5, 7, 8, 10}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}, {0, 4, 7, 8, 10}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}, {0, 3, 7, 8, 10}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 3, 5, 6, 7}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01529 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01529] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04601 :
    (({0, 3, 4, 5, 6, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 8, 12}, {4, 6, 7, 8, 12}, {4, 5, 7, 8, 12}, {4, 5, 6, 8, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 8}, {3, 6, 7, 8, 12}, {3, 5, 7, 8, 12}, {3, 5, 6, 8, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 8}, {3, 4, 7, 8, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 8}, {3, 4, 5, 8, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 8}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 8}, {3, 4, 5, 6, 7}, {0, 6, 7, 8, 12}, {0, 5, 7, 8, 12}, {0, 5, 6, 8, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 8}, {0, 4, 7, 8, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 8}, {0, 4, 5, 8, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}, {0, 3, 7, 8, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 8}, {0, 3, 5, 8, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 8}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 8}, {0, 3, 5, 6, 7}, {0, 3, 4, 8, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04601 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 8, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04601] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08697 :
    (({0, 3, 4, 5, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 8, 13}, {4, 6, 7, 8, 13}, {4, 5, 7, 8, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 8}, {3, 6, 7, 8, 13}, {3, 5, 7, 8, 13}, {3, 5, 6, 8, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 8}, {3, 4, 7, 8, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 8}, {3, 4, 5, 8, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 8}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 8}, {3, 4, 5, 6, 7}, {0, 6, 7, 8, 13}, {0, 5, 7, 8, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 8}, {0, 4, 7, 8, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 8}, {0, 4, 5, 8, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}, {0, 3, 7, 8, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 8}, {0, 3, 5, 8, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 8}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 8}, {0, 3, 5, 6, 7}, {0, 3, 4, 8, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08697 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 6, 7, 8, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 8} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 8} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 8} ∨
        polygon = {0, 3, 4, 5, 7} ∨
        polygon = {0, 3, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08697] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
