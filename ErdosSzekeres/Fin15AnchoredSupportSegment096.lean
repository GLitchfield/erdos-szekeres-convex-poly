module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 096. -/

theorem fin15Anchored_fiveFamily_mask29774 :
    (({1, 2, 3, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 6, 10, 13, 14}, {2, 6, 10, 12, 14}, {2, 6, 10, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {1, 10, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 10, 12, 14}, {1, 6, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29774 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 6, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29774] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13966 :
    (({1, 2, 3, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 7, 9, 12, 13}, {2, 7, 9, 10, 13}, {2, 7, 9, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {1, 9, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 7, 9, 12, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13966 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
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
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13966] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22158 :
    (({1, 2, 3, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {1, 9, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22158 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
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
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22158] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26254 :
    (({1, 2, 3, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {2, 9, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 10, 14}, {2, 7, 9, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {1, 9, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26254 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26254] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29326 :
    (({1, 2, 3, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {2, 9, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 9, 13, 14}, {2, 7, 9, 12, 14}, {2, 7, 9, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {1, 9, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29326 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29326] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29838 :
    (({1, 2, 3, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 7, 10, 13, 14}, {2, 7, 10, 12, 14}, {2, 7, 10, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {1, 10, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29838 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 12} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29838] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30222 :
    (({1, 2, 3, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {2, 10, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 9, 10, 13, 14}, {2, 9, 10, 12, 14}, {2, 9, 10, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {1, 10, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 9, 10, 13, 14}, {1, 9, 10, 12, 14}, {1, 9, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30222 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 12} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30222] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01782 :
    (({1, 2, 4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {4, 6, 7, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 6, 9, 10}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}, {2, 6, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 5, 6, 9, 10}, {2, 5, 6, 7, 10}, {2, 5, 6, 7, 9}, {2, 4, 7, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {1, 6, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {1, 2, 7, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01782 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01782] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04854 :
    (({1, 2, 4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {4, 6, 7, 9, 12}, {4, 5, 7, 9, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 9}, {2, 6, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 9}, {2, 4, 7, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {1, 6, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {1, 2, 7, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04854 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
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
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04854] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08950 :
    (({1, 2, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {4, 6, 7, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 9}, {2, 6, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 9}, {2, 4, 7, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 9}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {1, 6, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {1, 2, 7, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08950 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08950] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17142 :
    (({1, 2, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {4, 6, 7, 9, 14}, {4, 5, 7, 9, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 9}, {2, 6, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 9}, {2, 4, 7, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 9}, {2, 4, 5, 9, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {1, 6, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 9}, {1, 4, 7, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 9}, {1, 4, 5, 9, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {1, 2, 7, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 9}, {1, 2, 5, 9, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {1, 2, 4, 9, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17142 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 9} ∨
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
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17142] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05366 :
    (({1, 2, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {4, 6, 7, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}, {2, 6, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 7, 12}, {2, 5, 6, 7, 10}, {2, 4, 7, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {1, 6, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 4, 7, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {1, 2, 7, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05366 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {4, 5, 6, 7, 10} ∨
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
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05366] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09462 :
    (({1, 2, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {4, 6, 7, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}, {2, 6, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 10}, {2, 4, 7, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {1, 6, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}, {1, 4, 7, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {1, 2, 7, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09462 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 10} ∨
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
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09462] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17654 :
    (({1, 2, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {4, 6, 7, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 10}, {2, 6, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 10}, {2, 4, 7, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}, {2, 4, 5, 10, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {1, 6, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 10}, {1, 4, 7, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 4, 5, 10, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {1, 2, 7, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 5, 10, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {1, 2, 4, 10, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17654 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 10} ∨
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
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17654] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12534 :
    (({1, 2, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {4, 6, 7, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}, {2, 6, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 7, 13}, {2, 5, 6, 7, 12}, {2, 4, 7, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}, {1, 6, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 4, 7, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}, {1, 2, 7, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12534 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {4, 5, 6, 7, 12} ∨
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
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12534] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20726 :
    (({1, 2, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {4, 6, 7, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}, {2, 6, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 12}, {2, 4, 7, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}, {1, 6, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}, {1, 4, 7, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}, {1, 2, 7, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}, {1, 2, 4, 12, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20726 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 12} ∨
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
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20726] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24822 :
    (({1, 2, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {4, 6, 7, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}, {2, 6, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 7, 14}, {2, 5, 6, 7, 13}, {2, 4, 7, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 7}, {1, 6, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}, {1, 4, 7, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 7}, {1, 2, 7, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 7}, {1, 2, 4, 13, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24822 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {4, 5, 6, 7, 13} ∨
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
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24822] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask03702 :
    (({1, 2, 4, 5, 6, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 11}, {4, 6, 9, 10, 11}, {4, 5, 9, 10, 11}, {4, 5, 6, 10, 11}, {4, 5, 6, 9, 11}, {4, 5, 6, 9, 10}, {2, 6, 9, 10, 11}, {2, 5, 9, 10, 11}, {2, 5, 6, 10, 11}, {2, 5, 6, 9, 11}, {2, 5, 6, 9, 10}, {2, 4, 9, 10, 11}, {2, 4, 6, 10, 11}, {2, 4, 6, 9, 11}, {2, 4, 6, 9, 10}, {2, 4, 5, 10, 11}, {2, 4, 5, 9, 11}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 11}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {1, 6, 9, 10, 11}, {1, 5, 9, 10, 11}, {1, 5, 6, 10, 11}, {1, 5, 6, 9, 11}, {1, 5, 6, 9, 10}, {1, 4, 9, 10, 11}, {1, 4, 6, 10, 11}, {1, 4, 6, 9, 11}, {1, 4, 6, 9, 10}, {1, 4, 5, 10, 11}, {1, 4, 5, 9, 11}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 11}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 2, 9, 10, 11}, {1, 2, 6, 10, 11}, {1, 2, 6, 9, 11}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 11}, {1, 2, 5, 9, 11}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 11}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 4, 10, 11}, {1, 2, 4, 9, 11}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 11}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 11}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask03702 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 11} ∨
        polygon = {4, 6, 9, 10, 11} ∨
        polygon = {4, 5, 9, 10, 11} ∨
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {4, 5, 6, 9, 11} ∨
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {2, 6, 9, 10, 11} ∨
        polygon = {2, 5, 9, 10, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 5, 6, 9, 11} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 4, 9, 10, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 9, 11} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {1, 6, 9, 10, 11} ∨
        polygon = {1, 5, 9, 10, 11} ∨
        polygon = {1, 5, 6, 10, 11} ∨
        polygon = {1, 5, 6, 9, 11} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 4, 9, 10, 11} ∨
        polygon = {1, 4, 6, 10, 11} ∨
        polygon = {1, 4, 6, 9, 11} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 5, 10, 11} ∨
        polygon = {1, 4, 5, 9, 11} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 6, 11} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 2, 9, 10, 11} ∨
        polygon = {1, 2, 6, 10, 11} ∨
        polygon = {1, 2, 6, 9, 11} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 10, 11} ∨
        polygon = {1, 2, 5, 9, 11} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 11} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 10, 11} ∨
        polygon = {1, 2, 4, 9, 11} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 11} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 11} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask03702] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05750 :
    (({1, 2, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}, {2, 6, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 6, 10, 12}, {2, 5, 6, 9, 12}, {2, 5, 6, 9, 10}, {2, 4, 9, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 9, 10}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {1, 6, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 2, 9, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05750 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {4, 5, 6, 9, 10} ∨
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
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05750] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09846 :
    (({1, 2, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}, {2, 6, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 10}, {2, 4, 9, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 10}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {1, 6, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 2, 9, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09846 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 10} ∨
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
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09846] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18038 :
    (({1, 2, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 10}, {2, 6, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 10}, {2, 4, 9, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 10}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {1, 6, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 10}, {1, 4, 9, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 2, 9, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18038 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 10} ∨
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
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18038] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12918 :
    (({1, 2, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}, {2, 6, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 9, 13}, {2, 5, 6, 9, 12}, {2, 4, 9, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 9, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {1, 6, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 4, 9, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {1, 2, 9, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12918 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {4, 5, 6, 9, 12} ∨
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
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12918] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21110 :
    (({1, 2, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 12}, {2, 6, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 12}, {2, 4, 9, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {1, 6, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {1, 2, 9, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21110 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 12} ∨
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
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21110] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25206 :
    (({1, 2, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}, {2, 6, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 9, 14}, {2, 5, 6, 9, 13}, {2, 4, 9, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 9, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}, {1, 6, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {1, 2, 9, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25206 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {4, 5, 6, 9, 13} ∨
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
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25206] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13430 :
    (({1, 2, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}, {2, 6, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 6, 12, 13}, {2, 5, 6, 10, 13}, {2, 5, 6, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 10, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {1, 6, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 2, 10, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13430 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {4, 5, 6, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13430] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21622 :
    (({1, 2, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}, {2, 6, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {1, 6, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 2, 10, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21622 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 12} ∨
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
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21622] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25718 :
    (({1, 2, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}, {2, 6, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 10, 14}, {2, 5, 6, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 10, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {1, 6, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 2, 10, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25718 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {4, 5, 6, 10, 13} ∨
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
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25718] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28790 :
    (({1, 2, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}, {2, 6, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 6, 13, 14}, {2, 5, 6, 12, 14}, {2, 5, 6, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 6, 12, 14}, {2, 4, 6, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {1, 6, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 2, 12, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28790 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {4, 5, 6, 12, 13} ∨
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
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28790] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05814 :
    (({1, 2, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 9, 10}, {2, 7, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 5, 7, 10, 12}, {2, 5, 7, 9, 12}, {2, 5, 7, 9, 10}, {2, 4, 9, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 7, 9, 12}, {2, 4, 7, 9, 10}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {1, 7, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05814 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {4, 5, 7, 9, 10} ∨
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
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05814] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09910 :
    (({1, 2, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 10}, {2, 7, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 10}, {2, 4, 9, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 10}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {1, 7, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09910 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 10} ∨
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
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09910] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18102 :
    (({1, 2, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 10}, {2, 7, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 10}, {2, 4, 9, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 10}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {1, 7, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 10}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18102 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 10} ∨
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
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18102] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12982 :
    (({1, 2, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 12}, {2, 7, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 9, 13}, {2, 5, 7, 9, 12}, {2, 4, 9, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 9, 13}, {2, 4, 7, 9, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {1, 7, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12982 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {4, 5, 7, 9, 12} ∨
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
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12982] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21174 :
    (({1, 2, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 12}, {2, 7, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 12}, {2, 4, 9, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {1, 7, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21174 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 12} ∨
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
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21174] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25270 :
    (({1, 2, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 13}, {2, 7, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 9, 14}, {2, 5, 7, 9, 13}, {2, 4, 9, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 9, 14}, {2, 4, 7, 9, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}, {1, 7, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25270 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 13} ∨
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
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25270] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13494 :
    (({1, 2, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 10, 12}, {2, 7, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 7, 12, 13}, {2, 5, 7, 10, 13}, {2, 5, 7, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 7, 10, 13}, {2, 4, 7, 10, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {1, 7, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13494 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 10, 12} ∨
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
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13494] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21686 :
    (({1, 2, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 12}, {2, 7, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {1, 7, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21686 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 12} ∨
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
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21686] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25782 :
    (({1, 2, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 13}, {2, 7, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 10, 14}, {2, 5, 7, 10, 13}, {2, 4, 10, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 10, 14}, {2, 4, 7, 10, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {1, 7, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25782 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 13} ∨
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
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25782] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28854 :
    (({1, 2, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 12, 13}, {2, 7, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 5, 7, 13, 14}, {2, 5, 7, 12, 14}, {2, 5, 7, 12, 13}, {2, 4, 12, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 7, 12, 14}, {2, 4, 7, 12, 13}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {1, 7, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28854 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 12, 13} ∨
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
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28854] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13878 :
    (({1, 2, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}, {2, 9, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 5, 9, 12, 13}, {2, 5, 9, 10, 13}, {2, 5, 9, 10, 12}, {2, 4, 10, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 9, 10, 13}, {2, 4, 9, 10, 12}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {1, 9, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13878 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 12} ∨
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
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13878] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22070 :
    (({1, 2, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 12}, {2, 9, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 5, 9, 12, 14}, {2, 5, 9, 10, 14}, {2, 5, 9, 10, 12}, {2, 4, 10, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 9, 10, 14}, {2, 4, 9, 10, 12}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {1, 9, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22070 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 4, 5, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 12} ∨
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
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22070] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
