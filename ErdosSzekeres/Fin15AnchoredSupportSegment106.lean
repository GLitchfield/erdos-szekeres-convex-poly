module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 106. -/

theorem fin15Anchored_fiveFamily_mask30264 :
    (({3, 4, 5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {4, 10, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 9, 10, 13, 14}, {4, 9, 10, 12, 14}, {4, 9, 10, 12, 13}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30264 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 5, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30264] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask06104 :
    (({3, 4, 6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {6, 8, 9, 10, 12}, {6, 7, 9, 10, 12}, {6, 7, 8, 10, 12}, {6, 7, 8, 9, 12}, {6, 7, 8, 9, 10}, {4, 8, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 7, 8, 10, 12}, {4, 7, 8, 9, 12}, {4, 7, 8, 9, 10}, {4, 6, 9, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 8, 9, 12}, {4, 6, 8, 9, 10}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 10}, {4, 6, 7, 8, 9}, {3, 8, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {3, 6, 9, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {3, 4, 9, 10, 12}, {3, 4, 8, 10, 12}, {3, 4, 8, 9, 12}, {3, 4, 8, 9, 10}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 10}, {3, 4, 7, 8, 9}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06104 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06104] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10200 :
    (({3, 4, 6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {6, 8, 9, 10, 13}, {6, 7, 9, 10, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 10}, {4, 8, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 7, 8, 10, 13}, {4, 7, 8, 9, 13}, {4, 7, 8, 9, 10}, {4, 6, 9, 10, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 10}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 10}, {4, 6, 7, 8, 9}, {3, 8, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 10}, {3, 6, 9, 10, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 10}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {3, 4, 9, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 10}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 10}, {3, 4, 7, 8, 9}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10200 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10200] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18392 :
    (({3, 4, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {6, 8, 9, 10, 14}, {6, 7, 9, 10, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 10}, {4, 8, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 7, 8, 10, 14}, {4, 7, 8, 9, 14}, {4, 7, 8, 9, 10}, {4, 6, 9, 10, 14}, {4, 6, 8, 10, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 10}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 10}, {4, 6, 7, 8, 9}, {3, 8, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 10}, {3, 6, 9, 10, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 10}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {3, 4, 9, 10, 14}, {3, 4, 8, 10, 14}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 10}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 10}, {3, 4, 7, 8, 9}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18392 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 8, 10, 14} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 8, 10, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18392] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21464 :
    (({3, 4, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 14}, {6, 8, 9, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 12}, {4, 8, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 7, 8, 12, 14}, {4, 7, 8, 9, 14}, {4, 7, 8, 9, 12}, {4, 6, 9, 12, 14}, {4, 6, 8, 12, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 12}, {4, 6, 7, 12, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 9}, {3, 8, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 12}, {3, 6, 9, 12, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 12}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}, {3, 4, 9, 12, 14}, {3, 4, 8, 12, 14}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 12}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 9}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21464 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 8, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {4, 8, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 8, 12, 14} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 8, 12, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 8, 12, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21464] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25560 :
    (({3, 4, 6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {6, 8, 9, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 13}, {4, 8, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 8, 13, 14}, {4, 7, 8, 9, 14}, {4, 7, 8, 9, 13}, {4, 6, 9, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 13}, {4, 6, 7, 13, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 9}, {3, 8, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 8, 13, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 6, 9, 13, 14}, {3, 6, 8, 13, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 9}, {3, 4, 9, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 13}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 9}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25560 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {4, 8, 9, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 8, 13, 14} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 8, 13, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25560] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14040 :
    (({3, 4, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {4, 9, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 7, 9, 12, 13}, {4, 7, 9, 10, 13}, {4, 7, 9, 10, 12}, {4, 6, 10, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 9, 10, 13}, {4, 6, 9, 10, 12}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14040 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14040] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22232 :
    (({3, 4, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}, {4, 9, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 12}, {4, 6, 10, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 12}, {4, 6, 7, 12, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22232 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22232] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26328 :
    (({3, 4, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {4, 9, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 13}, {4, 6, 10, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 13}, {4, 6, 7, 13, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26328 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26328] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29400 :
    (({3, 4, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}, {4, 9, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 12, 13}, {4, 6, 12, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 12, 13}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29400 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29400] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29912 :
    (({3, 4, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}, {4, 10, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 10, 12, 14}, {4, 7, 10, 12, 13}, {4, 6, 12, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 10, 12, 14}, {4, 6, 10, 12, 13}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29912 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29912] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14168 :
    (({3, 4, 6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 8, 9, 12, 13}, {6, 8, 9, 10, 13}, {6, 8, 9, 10, 12}, {4, 9, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 8, 9, 12, 13}, {4, 8, 9, 10, 13}, {4, 8, 9, 10, 12}, {4, 6, 10, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 9, 10, 13}, {4, 6, 9, 10, 12}, {4, 6, 8, 12, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 10, 12}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 12}, {4, 6, 8, 9, 10}, {3, 9, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 8, 12, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 10, 12}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 12}, {3, 4, 8, 9, 10}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14168 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 8, 10, 12, 13} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 8, 12, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14168] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30296 :
    (({3, 4, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}, {4, 10, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 9, 10, 13, 14}, {4, 9, 10, 12, 14}, {4, 9, 10, 12, 13}, {4, 6, 12, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 10, 12, 14}, {4, 6, 10, 12, 13}, {4, 6, 9, 13, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 12, 13}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 13}, {4, 6, 9, 10, 12}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30296 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 6, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30296] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14232 :
    (({3, 4, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {7, 9, 10, 12, 13}, {7, 8, 10, 12, 13}, {7, 8, 9, 12, 13}, {7, 8, 9, 10, 13}, {7, 8, 9, 10, 12}, {4, 9, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 8, 9, 12, 13}, {4, 8, 9, 10, 13}, {4, 8, 9, 10, 12}, {4, 7, 10, 12, 13}, {4, 7, 9, 12, 13}, {4, 7, 9, 10, 13}, {4, 7, 9, 10, 12}, {4, 7, 8, 12, 13}, {4, 7, 8, 10, 13}, {4, 7, 8, 10, 12}, {4, 7, 8, 9, 13}, {4, 7, 8, 9, 12}, {4, 7, 8, 9, 10}, {3, 9, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 8, 12, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 10, 12}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 12}, {3, 4, 8, 9, 10}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 10}, {3, 4, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14232 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 7, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 8, 10, 12, 13} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 7, 8, 12, 13} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14232] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29592 :
    (({3, 4, 7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 12, 13}, {4, 9, 12, 13, 14}, {4, 8, 12, 13, 14}, {4, 8, 9, 13, 14}, {4, 8, 9, 12, 14}, {4, 8, 9, 12, 13}, {4, 7, 12, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 12, 13}, {4, 7, 8, 13, 14}, {4, 7, 8, 12, 14}, {4, 7, 8, 12, 13}, {4, 7, 8, 9, 14}, {4, 7, 8, 9, 13}, {4, 7, 8, 9, 12}, {3, 9, 12, 13, 14}, {3, 8, 12, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 12, 13}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 7, 8, 13, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 12, 13}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 12}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 8, 13, 14}, {3, 4, 8, 12, 14}, {3, 4, 8, 12, 13}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 12}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29592 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 7, 8, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 8, 12, 13, 14} ∨
        polygon = {4, 8, 9, 13, 14} ∨
        polygon = {4, 8, 9, 12, 14} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 7, 8, 13, 14} ∨
        polygon = {4, 7, 8, 12, 14} ∨
        polygon = {4, 7, 8, 12, 13} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 8, 12, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 8, 12, 14} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29592] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30360 :
    (({3, 4, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}, {4, 10, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 9, 10, 13, 14}, {4, 9, 10, 12, 14}, {4, 9, 10, 12, 13}, {4, 7, 12, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 10, 12, 14}, {4, 7, 10, 12, 13}, {4, 7, 9, 13, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 12, 13}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 13}, {4, 7, 9, 10, 12}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30360 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 4, 7, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 4, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30360] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18408 :
    (({3, 5, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {6, 8, 9, 10, 14}, {6, 7, 9, 10, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 10}, {5, 8, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 10}, {5, 6, 9, 10, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 10}, {5, 6, 7, 10, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 10}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 10}, {5, 6, 7, 8, 9}, {3, 8, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 10}, {3, 6, 9, 10, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 10}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {3, 5, 9, 10, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 10}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 10}, {3, 5, 6, 8, 9}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}, {3, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18408 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18408] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13288 :
    (({3, 5, 6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 13}, {6, 8, 9, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 12}, {5, 8, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 8, 12, 13}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 12}, {5, 6, 9, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 12}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 9}, {3, 8, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 8, 12, 13}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 12}, {3, 6, 9, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 12}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}, {3, 5, 9, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 12}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 9}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 9}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}, {3, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13288 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 8, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13288] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21480 :
    (({3, 5, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 14}, {6, 8, 9, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 12}, {5, 8, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 12}, {5, 6, 9, 12, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 12}, {5, 6, 7, 12, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 9}, {3, 8, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 12}, {3, 6, 9, 12, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 12}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}, {3, 5, 9, 12, 14}, {3, 5, 8, 12, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 12}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 9}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 9}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}, {3, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21480 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 8, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {5, 8, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 8, 12, 14} ∨
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21480] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25576 :
    (({3, 5, 6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {6, 8, 9, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 13}, {5, 8, 9, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 13}, {5, 6, 9, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 9}, {3, 8, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 8, 13, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 6, 9, 13, 14}, {3, 6, 8, 13, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 9}, {3, 5, 9, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 9}, {3, 5, 6, 13, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 9}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 9}, {3, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25576 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25576] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13800 :
    (({3, 5, 6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 10, 12}, {5, 8, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 8, 12, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 10, 12}, {5, 6, 10, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 10}, {3, 8, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {3, 6, 10, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {3, 5, 10, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 10}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13800 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13800] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26088 :
    (({3, 5, 6, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 13}, {5, 8, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 13}, {5, 6, 10, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 10}, {3, 8, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 8, 13, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 13}, {3, 6, 10, 13, 14}, {3, 6, 8, 13, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 10}, {3, 5, 10, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 10}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26088 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 8, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26088] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29160 :
    (({3, 5, 6, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 12, 13}, {5, 8, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 12, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 12}, {3, 8, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 8, 13, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 8, 13, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 12, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 12}, {3, 5, 12, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 12, 14}, {3, 5, 8, 12, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 12}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29160 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 8, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {6, 8, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {5, 8, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 8, 12, 14} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {3, 8, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29160] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14056 :
    (({3, 5, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {5, 9, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14056 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14056] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22248 :
    (({3, 5, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}, {5, 9, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 12}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {5, 6, 7, 12, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22248 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22248] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26344 :
    (({3, 5, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {5, 9, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26344 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26344] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29416 :
    (({3, 5, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}, {5, 9, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29416 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29416] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29928 :
    (({3, 5, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29928 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29928] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22376 :
    (({3, 5, 6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 12}, {5, 9, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 12}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {5, 6, 8, 12, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 12}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 12}, {5, 6, 8, 9, 10}, {3, 9, 10, 12, 14}, {3, 8, 10, 12, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 12}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {3, 6, 8, 12, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 5, 8, 12, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 10}, {3, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22376 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 8, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 8, 9, 12, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 8, 12, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22376] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26472 :
    (({3, 5, 6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 13}, {5, 9, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 9, 13, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 13}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {5, 6, 8, 13, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 10}, {3, 9, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 13}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 8, 13, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 13}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 10}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 8, 13, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 10}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 10}, {3, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26472 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 8, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26472] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30056 :
    (({3, 5, 6, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 10, 12, 14}, {6, 8, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 10, 12, 14}, {5, 8, 10, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {5, 6, 8, 13, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}, {3, 10, 12, 13, 14}, {3, 8, 12, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 10, 12, 14}, {3, 8, 10, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 6, 8, 13, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 8, 13, 14}, {3, 5, 8, 12, 14}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 5, 6, 8, 14}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30056 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 8, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 8, 12, 13, 14} ∨
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 8, 12, 13, 14} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 8, 12, 14} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 8, 12, 13, 14} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 8, 14} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30056] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30312 :
    (({3, 5, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30312 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 6, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30312] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14248 :
    (({3, 5, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {7, 9, 10, 12, 13}, {7, 8, 10, 12, 13}, {7, 8, 9, 12, 13}, {7, 8, 9, 10, 13}, {7, 8, 9, 10, 12}, {5, 9, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 8, 9, 12, 13}, {5, 8, 9, 10, 13}, {5, 8, 9, 10, 12}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {5, 7, 8, 12, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}, {3, 9, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14248 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 7, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14248] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22440 :
    (({3, 5, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {7, 9, 10, 12, 14}, {7, 8, 10, 12, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 12}, {5, 9, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 12}, {5, 7, 10, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 12}, {5, 7, 8, 12, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}, {3, 9, 10, 12, 14}, {3, 8, 10, 12, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 12}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {3, 7, 8, 12, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 5, 8, 12, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22440 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 7, 8, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 8, 9, 12, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22440] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26536 :
    (({3, 5, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {7, 9, 10, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 13}, {5, 9, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 9, 13, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 13}, {5, 7, 10, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {5, 7, 8, 13, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 13}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 10}, {3, 9, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 13}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 7, 8, 13, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 13}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 10}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 8, 13, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 10}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26536 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 7, 8, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26536] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30120 :
    (({3, 5, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 10, 12, 14}, {7, 8, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 10, 12, 14}, {5, 8, 10, 12, 13}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {5, 7, 8, 13, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 12, 13}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 13}, {5, 7, 8, 10, 12}, {3, 10, 12, 13, 14}, {3, 8, 12, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 10, 12, 14}, {3, 8, 10, 12, 13}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 7, 8, 13, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 8, 13, 14}, {3, 5, 8, 12, 14}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30120 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 7, 8, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 8, 12, 13, 14} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 8, 12, 13, 14} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30120] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30376 :
    (({3, 5, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30376 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 7, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30376] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30504 :
    (({3, 5, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {8, 10, 12, 13, 14}, {8, 9, 12, 13, 14}, {8, 9, 10, 13, 14}, {8, 9, 10, 12, 14}, {8, 9, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {5, 8, 12, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 10, 12, 14}, {5, 8, 10, 12, 13}, {5, 8, 9, 13, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 12, 13}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 13}, {5, 8, 9, 10, 12}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 8, 12, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 10, 12, 14}, {3, 8, 10, 12, 13}, {3, 8, 9, 13, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 8, 13, 14}, {3, 5, 8, 12, 14}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30504 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 5, 8, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {8, 10, 12, 13, 14} ∨
        polygon = {8, 9, 12, 13, 14} ∨
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 8, 12, 13, 14} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {5, 8, 9, 12, 14} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 8, 12, 13, 14} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 5, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30504] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26568 :
    (({3, 6, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {7, 9, 10, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 13}, {6, 9, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 13}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {6, 7, 8, 13, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 13}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 10}, {3, 9, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 13}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 7, 8, 13, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 13}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 10}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 8, 13, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 13}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 10}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26568 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 6, 7, 8, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 6, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26568] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29640 :
    (({3, 6, 7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 12, 13}, {6, 9, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 12, 13}, {6, 7, 12, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}, {6, 7, 8, 13, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 12, 13}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 12}, {3, 9, 12, 13, 14}, {3, 8, 12, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 12, 13}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 7, 8, 13, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 12, 13}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 12}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 6, 8, 13, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 12, 13}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 12}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29640 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {3, 6, 7, 8, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 8, 12, 13, 14} ∨
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 8, 12, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 8, 13, 14} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({3, 6, 7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29640] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
