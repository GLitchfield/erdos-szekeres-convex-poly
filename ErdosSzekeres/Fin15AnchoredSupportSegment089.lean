module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 089. -/

theorem fin15Anchored_fiveFamily_mask13673 :
    (({0, 3, 5, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}, {3, 8, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}, {3, 5, 10, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 12}, {3, 5, 6, 8, 10}, {0, 8, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13673 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 6, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 8, 13} ∨
        polygon = {3, 5, 6, 8, 12} ∨
        polygon = {3, 5, 6, 8, 10} ∨
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
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13673] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13929 :
    (({0, 3, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {0, 9, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13929 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 6, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
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
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13929] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22121 :
    (({0, 3, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {0, 9, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22121 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 6, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
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
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22121] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26217 :
    (({0, 3, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {0, 9, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26217 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 6, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
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
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26217] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29289 :
    (({0, 3, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {0, 9, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29289 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 6, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 9, 13, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
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
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29289] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29801 :
    (({0, 3, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}, {0, 10, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29801 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 6, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 6, 12, 13, 14} ∨
        polygon = {5, 6, 10, 13, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 12} ∨
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
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29801] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask06057 :
    (({0, 3, 5, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {5, 8, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}, {3, 8, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {3, 5, 9, 10, 12}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}, {0, 8, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 5, 9, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06057 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
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
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06057] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10153 :
    (({0, 3, 5, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {5, 8, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 10}, {3, 8, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 10}, {3, 5, 9, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 10}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}, {0, 8, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 5, 9, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10153 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 8, 13} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 9} ∨
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
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10153] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18345 :
    (({0, 3, 5, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {5, 8, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 10}, {3, 8, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 10}, {3, 5, 9, 10, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 10}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}, {0, 8, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 10}, {0, 5, 9, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 3, 9, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18345 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 10} ∨
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
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18345] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25513 :
    (({0, 3, 5, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {5, 8, 9, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 13}, {3, 8, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 8, 13, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}, {3, 5, 9, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 9}, {0, 8, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 8, 13, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}, {0, 5, 9, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 9}, {0, 3, 9, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 9}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25513 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 9, 14} ∨
        polygon = {3, 7, 8, 9, 13} ∨
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
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25513] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13737 :
    (({0, 3, 5, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 8, 12, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 10, 12}, {3, 8, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {3, 5, 10, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {0, 8, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13737 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 8, 12, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 12} ∨
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
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13737] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21929 :
    (({0, 3, 5, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 12}, {3, 8, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 12}, {3, 5, 10, 12, 14}, {3, 5, 8, 12, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 12}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 12}, {3, 5, 7, 8, 10}, {0, 8, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 3, 10, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 12}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21929 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 8, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 8, 14} ∨
        polygon = {3, 5, 7, 8, 12} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21929] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26025 :
    (({0, 3, 5, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 13}, {3, 8, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 8, 13, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 13}, {3, 5, 10, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 8, 14}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}, {0, 8, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 8, 13, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 3, 10, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26025 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 8, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 13} ∨
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
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26025] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13993 :
    (({0, 3, 5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13993 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
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
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13993] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22185 :
    (({0, 3, 5, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22185 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 12} ∨
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
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22185] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26281 :
    (({0, 3, 5, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26281 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
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
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26281] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29353 :
    (({0, 3, 5, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29353 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
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
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29353] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask15529 :
    (({0, 3, 5, 7, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 12, 13}, {5, 10, 11, 12, 13}, {5, 7, 11, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 10, 11, 13}, {5, 7, 10, 11, 12}, {3, 10, 11, 12, 13}, {3, 7, 11, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 10, 11, 13}, {3, 7, 10, 11, 12}, {3, 5, 11, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 10, 11, 13}, {3, 5, 10, 11, 12}, {3, 5, 7, 12, 13}, {3, 5, 7, 11, 13}, {3, 5, 7, 11, 12}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 5, 7, 10, 11}, {0, 10, 11, 12, 13}, {0, 7, 11, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 10, 11, 13}, {0, 7, 10, 11, 12}, {0, 5, 11, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 10, 11, 13}, {0, 5, 10, 11, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 11, 13}, {0, 5, 7, 11, 12}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 10, 11}, {0, 3, 11, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 10, 11, 13}, {0, 3, 10, 11, 12}, {0, 3, 7, 12, 13}, {0, 3, 7, 11, 13}, {0, 3, 7, 11, 12}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 10, 11}, {0, 3, 5, 12, 13}, {0, 3, 5, 11, 13}, {0, 3, 5, 11, 12}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 10, 11}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 11}, {0, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask15529 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 10, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 10, 11, 12, 13} ∨
        polygon = {5, 10, 11, 12, 13} ∨
        polygon = {5, 7, 11, 12, 13} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {5, 7, 10, 11, 13} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {3, 10, 11, 12, 13} ∨
        polygon = {3, 7, 11, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 11, 13} ∨
        polygon = {3, 7, 10, 11, 12} ∨
        polygon = {3, 5, 11, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 10, 11, 13} ∨
        polygon = {3, 5, 10, 11, 12} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 11, 13} ∨
        polygon = {3, 5, 7, 11, 12} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 11} ∨
        polygon = {0, 10, 11, 12, 13} ∨
        polygon = {0, 7, 11, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 10, 11, 13} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 5, 11, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 10, 11, 13} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 11, 13} ∨
        polygon = {0, 5, 7, 11, 12} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 11} ∨
        polygon = {0, 3, 11, 12, 13} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 10, 11, 13} ∨
        polygon = {0, 3, 10, 11, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 11, 13} ∨
        polygon = {0, 3, 7, 11, 12} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 10, 11} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 11, 13} ∨
        polygon = {0, 3, 5, 11, 12} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 10, 11} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 11} ∨
        polygon = {0, 3, 5, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask15529] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29865 :
    (({0, 3, 5, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29865 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
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
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29865] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14121 :
    (({0, 3, 5, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 8, 9, 12, 13}, {5, 8, 9, 10, 13}, {5, 8, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {0, 9, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14121 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 12} ∨
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
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14121] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22313 :
    (({0, 3, 5, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 8, 10, 12, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 12}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 5, 8, 12, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {0, 9, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 12}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 8, 12, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 8, 12, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22313 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 8, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 8, 9, 12, 14} ∨
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 8, 9, 12, 14} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 8, 9, 10, 12} ∨
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
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22313] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30249 :
    (({0, 3, 5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30249 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 5, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 13} ∨
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
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30249] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask06089 :
    (({0, 3, 6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {6, 8, 9, 10, 12}, {6, 7, 9, 10, 12}, {6, 7, 8, 10, 12}, {6, 7, 8, 9, 12}, {6, 7, 8, 9, 10}, {3, 8, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {3, 6, 9, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {0, 8, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 6, 9, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06089 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
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
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06089] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10185 :
    (({0, 3, 6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {6, 8, 9, 10, 13}, {6, 7, 9, 10, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 10}, {3, 8, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 10}, {3, 6, 9, 10, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 10}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {0, 8, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 6, 9, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10185 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 10} ∨
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
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10185] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18377 :
    (({0, 3, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {6, 8, 9, 10, 14}, {6, 7, 9, 10, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 10}, {3, 8, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 10}, {3, 6, 9, 10, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 10}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 10}, {3, 6, 7, 8, 9}, {0, 8, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 10}, {0, 6, 9, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 10}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 3, 9, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 10}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18377 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 10} ∨
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
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18377] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13257 :
    (({0, 3, 6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 13}, {6, 8, 9, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 12}, {3, 8, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 8, 12, 13}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 12}, {3, 6, 9, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 12}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}, {0, 8, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 6, 9, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 3, 9, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 12}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13257 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 8, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 12} ∨
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
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13257] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21449 :
    (({0, 3, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 14}, {6, 8, 9, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 12}, {3, 8, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 12}, {3, 6, 9, 12, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 12}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}, {0, 8, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 12}, {0, 6, 9, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 3, 9, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 12}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21449 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 8, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 12} ∨
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
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21449] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13769 :
    (({0, 3, 6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 10, 12}, {3, 8, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {3, 6, 10, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {0, 8, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 6, 10, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13769 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 10, 12} ∨
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
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13769] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21961 :
    (({0, 3, 6, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 12}, {3, 8, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 8, 12, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 12}, {3, 6, 10, 12, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 12}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {3, 6, 7, 8, 14}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {0, 8, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 12}, {0, 6, 10, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 3, 10, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 12}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21961 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 8, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {3, 8, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 8, 12, 14} ∨
        polygon = {3, 7, 8, 10, 14} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 8, 12, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21961] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14025 :
    (({0, 3, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14025 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 12} ∨
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
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14025] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22217 :
    (({0, 3, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22217 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 12} ∨
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
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22217] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26313 :
    (({0, 3, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26313 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 13} ∨
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
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26313] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29385 :
    (({0, 3, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29385 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 13} ∨
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
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29385] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29897 :
    (({0, 3, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29897 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 13} ∨
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
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29897] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14153 :
    (({0, 3, 6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 8, 9, 12, 13}, {6, 8, 9, 10, 13}, {6, 8, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {0, 9, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14153 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 12} ∨
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
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14153] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22345 :
    (({0, 3, 6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 8, 10, 12, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 12}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {3, 6, 8, 12, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {0, 9, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 12}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 6, 8, 12, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 8, 12, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22345 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 8, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 12} ∨
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
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22345] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26441 :
    (({0, 3, 6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 8, 9, 13, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 13}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 8, 13, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 13}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 10}, {0, 9, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 8, 13, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 8, 13, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26441 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 8, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 13} ∨
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
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 10} ∨
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
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26441] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30281 :
    (({0, 3, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30281 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 6, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 13} ∨
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
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30281] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14217 :
    (({0, 3, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {7, 9, 10, 12, 13}, {7, 8, 10, 12, 13}, {7, 8, 9, 12, 13}, {7, 8, 9, 10, 13}, {7, 8, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 7, 8, 12, 13}, {3, 7, 8, 10, 13}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 13}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {0, 9, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14217 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 7, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {7, 8, 9, 10, 12} ∨
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
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14217] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22409 :
    (({0, 3, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {7, 9, 10, 12, 14}, {7, 8, 10, 12, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 8, 10, 12, 14}, {3, 8, 9, 12, 14}, {3, 8, 9, 10, 14}, {3, 8, 9, 10, 12}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {3, 7, 8, 12, 14}, {3, 7, 8, 10, 14}, {3, 7, 8, 10, 12}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 12}, {3, 7, 8, 9, 10}, {0, 9, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 12}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 7, 8, 12, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 8, 12, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22409 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 7, 8, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {7, 8, 9, 10, 12} ∨
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
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22409] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
