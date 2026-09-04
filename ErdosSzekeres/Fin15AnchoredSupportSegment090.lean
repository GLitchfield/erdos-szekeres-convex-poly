module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 090. -/

theorem fin15Anchored_fiveFamily_mask26505 :
    (({0, 3, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {7, 9, 10, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 13}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 7, 8, 13, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 13}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 10}, {0, 9, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 8, 13, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 8, 13, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26505 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 7, 8, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {7, 8, 9, 10, 13} ∨
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
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 10} ∨
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
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26505] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30089 :
    (({0, 3, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 10, 12, 14}, {7, 8, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 8, 12, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 10, 12, 14}, {3, 8, 10, 12, 13}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 7, 8, 13, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {0, 10, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 8, 13, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 8, 13, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30089 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 7, 8, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {7, 8, 10, 12, 13} ∨
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
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 8, 12, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30089] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30345 :
    (({0, 3, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30345 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 7, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 13} ∨
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
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30345] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask02033 :
    (({0, 4, 5, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 10}, {5, 7, 8, 9, 10}, {5, 6, 8, 9, 10}, {5, 6, 7, 9, 10}, {5, 6, 7, 8, 10}, {5, 6, 7, 8, 9}, {4, 7, 8, 9, 10}, {4, 6, 8, 9, 10}, {4, 6, 7, 9, 10}, {4, 6, 7, 8, 10}, {4, 6, 7, 8, 9}, {4, 5, 8, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 7, 8, 10}, {4, 5, 7, 8, 9}, {4, 5, 6, 9, 10}, {4, 5, 6, 8, 10}, {4, 5, 6, 8, 9}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}, {4, 5, 6, 7, 8}, {0, 7, 8, 9, 10}, {0, 6, 8, 9, 10}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 5, 8, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}, {0, 4, 8, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask02033 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask02033] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05105 :
    (({0, 4, 5, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 12}, {5, 7, 8, 9, 12}, {5, 6, 8, 9, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 9}, {4, 7, 8, 9, 12}, {4, 6, 8, 9, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 9}, {4, 5, 8, 9, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 9}, {4, 5, 6, 9, 12}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 9}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 9}, {4, 5, 6, 7, 8}, {0, 7, 8, 9, 12}, {0, 6, 8, 9, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 5, 8, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}, {0, 5, 6, 9, 12}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}, {0, 4, 8, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05105 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05105] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09201 :
    (({0, 4, 5, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 13}, {5, 7, 8, 9, 13}, {5, 6, 8, 9, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 9}, {4, 7, 8, 9, 13}, {4, 6, 8, 9, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 9}, {4, 5, 8, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 9}, {4, 5, 6, 9, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 9}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 9}, {4, 5, 6, 7, 8}, {0, 7, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 9}, {0, 5, 8, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 9}, {0, 5, 6, 9, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}, {0, 4, 8, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 4, 5, 9, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09201 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09201] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05617 :
    (({0, 4, 5, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {5, 7, 8, 10, 12}, {5, 6, 8, 10, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 10}, {4, 7, 8, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 10}, {4, 5, 8, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 10}, {4, 5, 6, 10, 12}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 10}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 8}, {0, 7, 8, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 5, 8, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}, {0, 4, 8, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05617 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05617] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09713 :
    (({0, 4, 5, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 13}, {5, 7, 8, 10, 13}, {5, 6, 8, 10, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 10}, {4, 7, 8, 10, 13}, {4, 6, 8, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 10}, {4, 5, 8, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 10}, {4, 5, 6, 10, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 10}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 8}, {0, 7, 8, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 5, 8, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 5, 6, 10, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}, {0, 4, 8, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09713 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09713] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17905 :
    (({0, 4, 5, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 14}, {5, 7, 8, 10, 14}, {5, 6, 8, 10, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 10}, {4, 7, 8, 10, 14}, {4, 6, 8, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 10}, {4, 5, 8, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 10}, {4, 5, 6, 10, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 10}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 8}, {0, 7, 8, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 10}, {0, 5, 8, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 10}, {0, 5, 6, 10, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}, {0, 4, 8, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 4, 5, 10, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17905 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {4, 7, 8, 10, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17905] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20977 :
    (({0, 4, 5, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 12, 14}, {5, 7, 8, 12, 14}, {5, 6, 8, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 12}, {4, 7, 8, 12, 14}, {4, 6, 8, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 12}, {4, 5, 8, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 12}, {4, 5, 6, 12, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 12}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 8}, {0, 7, 8, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 5, 8, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 12}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 8}, {0, 4, 8, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 8}, {0, 4, 5, 12, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20977 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 6, 8, 12, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {4, 7, 8, 12, 14} ∨
        polygon = {4, 6, 8, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 5, 8, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20977] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25073 :
    (({0, 4, 5, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 13, 14}, {5, 7, 8, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 13}, {4, 7, 8, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 13}, {4, 5, 8, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 13}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 8}, {0, 7, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}, {0, 5, 8, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 8}, {0, 4, 8, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 8}, {0, 4, 5, 13, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25073 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {4, 7, 8, 13, 14} ∨
        polygon = {4, 6, 8, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 8} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 8} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 8} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 8} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25073] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05873 :
    (({0, 4, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 6, 9, 10, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {4, 7, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {4, 5, 9, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 9, 10}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}, {0, 7, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 5, 9, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05873 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05873] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09969 :
    (({0, 4, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 6, 9, 10, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}, {4, 7, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {4, 5, 9, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 10}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}, {0, 7, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 5, 9, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09969 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09969] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18161 :
    (({0, 4, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 6, 9, 10, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 10}, {4, 7, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}, {4, 5, 9, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 10}, {4, 5, 6, 10, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 10}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}, {0, 7, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}, {0, 5, 9, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18161 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18161] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13041 :
    (({0, 4, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {4, 7, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {4, 5, 9, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 12}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 9}, {0, 7, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 5, 9, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13041 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13041] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21233 :
    (({0, 4, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {4, 7, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}, {4, 5, 9, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 12}, {4, 5, 6, 12, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 12}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 9}, {0, 7, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 5, 9, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21233 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21233] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25329 :
    (({0, 4, 5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {5, 7, 9, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {4, 7, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {4, 5, 9, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 9}, {0, 7, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 5, 9, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25329 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25329] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask07409 :
    (({0, 4, 5, 6, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 11, 12}, {5, 7, 10, 11, 12}, {5, 6, 10, 11, 12}, {5, 6, 7, 11, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 10, 11}, {4, 7, 10, 11, 12}, {4, 6, 10, 11, 12}, {4, 6, 7, 11, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 10, 11}, {4, 5, 10, 11, 12}, {4, 5, 7, 11, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 10, 11}, {4, 5, 6, 11, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 10, 11}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 11}, {4, 5, 6, 7, 10}, {0, 7, 10, 11, 12}, {0, 6, 10, 11, 12}, {0, 6, 7, 11, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 10, 11}, {0, 5, 10, 11, 12}, {0, 5, 7, 11, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 10, 11}, {0, 5, 6, 11, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 10, 11}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 11}, {0, 5, 6, 7, 10}, {0, 4, 10, 11, 12}, {0, 4, 7, 11, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 10, 11}, {0, 4, 6, 11, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 10, 11}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 11}, {0, 4, 6, 7, 10}, {0, 4, 5, 11, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 10, 11}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 11}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 11}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07409 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 11, 12} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {4, 5, 10, 11, 12} ∨
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {4, 5, 6, 11, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 11} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 6, 10, 11, 12} ∨
        polygon = {0, 6, 7, 11, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 11} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 5, 7, 11, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 11} ∨
        polygon = {0, 5, 6, 11, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 10, 11} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 11} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 4, 10, 11, 12} ∨
        polygon = {0, 4, 7, 11, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 10, 11} ∨
        polygon = {0, 4, 6, 11, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 10, 11} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 11} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 11, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 10, 11} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 11} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 11} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07409] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13553 :
    (({0, 4, 5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {4, 7, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}, {4, 5, 10, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 10, 12}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {0, 7, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13553 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
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
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13553] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21745 :
    (({0, 4, 5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}, {4, 7, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 12}, {4, 5, 10, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 12}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {0, 7, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21745 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
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
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21745] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25841 :
    (({0, 4, 5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {4, 7, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}, {4, 5, 10, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}, {0, 7, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25841 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 10} ∨
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
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25841] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28913 :
    (({0, 4, 5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {4, 7, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}, {4, 5, 12, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 12, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}, {0, 7, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28913 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 12} ∨
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
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28913] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask06001 :
    (({0, 4, 5, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 12}, {5, 8, 9, 10, 12}, {5, 6, 9, 10, 12}, {5, 6, 8, 10, 12}, {5, 6, 8, 9, 12}, {5, 6, 8, 9, 10}, {4, 8, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 8, 9, 12}, {4, 6, 8, 9, 10}, {4, 5, 9, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 8, 9, 12}, {4, 5, 8, 9, 10}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 10}, {4, 5, 6, 8, 9}, {0, 8, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 5, 9, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 4, 9, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 8, 9, 12}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06001 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06001] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10097 :
    (({0, 4, 5, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 13}, {5, 8, 9, 10, 13}, {5, 6, 9, 10, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 10}, {4, 8, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 10}, {4, 5, 9, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 10}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 10}, {4, 5, 6, 8, 9}, {0, 8, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 5, 9, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 4, 9, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10097 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10097] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18289 :
    (({0, 4, 5, 6, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 14}, {5, 8, 9, 10, 14}, {5, 6, 9, 10, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 10}, {4, 8, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 8, 10, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 10}, {4, 5, 9, 10, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 9, 14}, {4, 5, 8, 9, 10}, {4, 5, 6, 10, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 10}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 10}, {4, 5, 6, 8, 9}, {0, 8, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 10}, {0, 5, 9, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 10}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 4, 9, 10, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18289 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18289] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13169 :
    (({0, 4, 5, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 13}, {5, 8, 9, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 12}, {4, 8, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 8, 12, 13}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 12}, {4, 5, 9, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 12}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 9}, {0, 8, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 5, 9, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 9}, {0, 4, 9, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13169 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 8, 12, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13169] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25457 :
    (({0, 4, 5, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 13, 14}, {5, 8, 9, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 13}, {4, 8, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 13}, {4, 5, 9, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 9, 14}, {4, 5, 8, 9, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 9}, {0, 8, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 5, 9, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 9}, {0, 4, 9, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25457 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 8, 9, 14} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {4, 8, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 8, 13, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 9} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25457] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13681 :
    (({0, 4, 5, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}, {4, 8, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 8, 12, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 10, 12}, {4, 5, 10, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 10, 12}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 10}, {0, 8, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 4, 10, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 10, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13681 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {4, 8, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 8, 12, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13681] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21873 :
    (({0, 4, 5, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 12}, {4, 8, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 8, 12, 14}, {4, 6, 8, 10, 14}, {4, 6, 8, 10, 12}, {4, 5, 10, 12, 14}, {4, 5, 8, 12, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 10, 12}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 10}, {0, 8, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 4, 10, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 10, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21873 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 8, 12, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {4, 8, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 8, 12, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 8, 12, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 12} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 8, 12, 14} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21873] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25969 :
    (({0, 4, 5, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}, {4, 8, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 8, 10, 14}, {4, 6, 8, 10, 13}, {4, 5, 10, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 10, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 10}, {0, 8, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 4, 10, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 10, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25969 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 8, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 8, 13, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {4, 8, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 8, 13, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 8, 14} ∨
        polygon = {4, 5, 6, 8, 13} ∨
        polygon = {4, 5, 6, 8, 10} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 13} ∨
        polygon = {0, 4, 6, 8, 10} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25969] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13937 :
    (({0, 4, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {4, 9, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 9, 10, 13}, {4, 6, 9, 10, 12}, {4, 5, 10, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {0, 9, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 4, 10, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13937 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
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
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13937] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22129 :
    (({0, 4, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {4, 9, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 12}, {4, 5, 10, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 12}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {0, 9, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 4, 10, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22129 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
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
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22129] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26225 :
    (({0, 4, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {4, 9, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 13}, {4, 5, 10, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}, {0, 9, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 4, 10, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26225 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 10} ∨
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
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26225] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29297 :
    (({0, 4, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {4, 9, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 12, 13}, {4, 5, 12, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {0, 9, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 4, 12, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29297 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 12} ∨
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
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29297] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29809 :
    (({0, 4, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {4, 10, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 10, 12, 14}, {4, 6, 10, 12, 13}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {0, 10, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29809 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 6, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 10, 12} ∨
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
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29809] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask06065 :
    (({0, 4, 5, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {5, 8, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}, {4, 8, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 7, 8, 10, 12}, {4, 7, 8, 9, 12}, {4, 7, 8, 9, 10}, {4, 5, 9, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 8, 9, 12}, {4, 5, 8, 9, 10}, {4, 5, 7, 10, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 9, 10}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 10}, {4, 5, 7, 8, 9}, {0, 8, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 5, 9, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 4, 9, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 8, 9, 12}, {0, 4, 8, 9, 10}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06065 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06065] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10161 :
    (({0, 4, 5, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {5, 8, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 10}, {4, 8, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 7, 8, 10, 13}, {4, 7, 8, 9, 13}, {4, 7, 8, 9, 10}, {4, 5, 9, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 10}, {4, 5, 7, 10, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 10}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 10}, {4, 5, 7, 8, 9}, {0, 8, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 5, 9, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 4, 9, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 10}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10161 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 7, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10161] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18353 :
    (({0, 4, 5, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {5, 8, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 10}, {4, 8, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 7, 8, 10, 14}, {4, 7, 8, 9, 14}, {4, 7, 8, 9, 10}, {4, 5, 9, 10, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 9, 14}, {4, 5, 8, 9, 10}, {4, 5, 7, 10, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 10}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 10}, {4, 5, 7, 8, 9}, {0, 8, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 10}, {0, 5, 9, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 4, 9, 10, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 10}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18353 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 7, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {4, 8, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 8, 10, 14} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 10} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18353] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13233 :
    (({0, 4, 5, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 13}, {5, 8, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 8, 12, 13}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 12}, {4, 8, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 7, 8, 12, 13}, {4, 7, 8, 9, 13}, {4, 7, 8, 9, 12}, {4, 5, 9, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 12}, {4, 5, 7, 12, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 12}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 9}, {0, 8, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 5, 9, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}, {0, 4, 9, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 12}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13233 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 7, 8, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 7, 8, 12, 13} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 8, 13} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13233] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21425 :
    (({0, 4, 5, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 14}, {5, 8, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 12}, {4, 8, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 7, 8, 12, 14}, {4, 7, 8, 9, 14}, {4, 7, 8, 9, 12}, {4, 5, 9, 12, 14}, {4, 5, 8, 12, 14}, {4, 5, 8, 9, 14}, {4, 5, 8, 9, 12}, {4, 5, 7, 12, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 12}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 9}, {0, 8, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 12}, {0, 5, 9, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}, {0, 4, 9, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 12}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21425 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 4, 5, 7, 8, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {5, 8, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {4, 8, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 8, 12, 14} ∨
        polygon = {4, 7, 8, 9, 14} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 8, 12, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 8, 14} ∨
        polygon = {4, 5, 7, 8, 12} ∨
        polygon = {4, 5, 7, 8, 9} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 8, 12, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 4, 5, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21425] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
