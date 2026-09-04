module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 087. -/

theorem fin15Anchored_fiveFamily_mask18105 :
    (({0, 3, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 10}, {3, 7, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {0, 7, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18105 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 9, 10, 14} →
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
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18105] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12985 :
    (({0, 3, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 12}, {3, 7, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {0, 7, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12985 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 9, 12, 13} →
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
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12985] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21177 :
    (({0, 3, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 12}, {3, 7, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {3, 4, 9, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {0, 7, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21177 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 9, 12, 14} →
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
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21177] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25273 :
    (({0, 3, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 13}, {3, 7, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {0, 7, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25273 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 9, 13, 14} →
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
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25273] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13497 :
    (({0, 3, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 10, 12}, {3, 7, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {0, 7, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13497 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 10, 12, 13} →
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
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13497] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21689 :
    (({0, 3, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 12}, {3, 7, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {0, 7, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21689 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 10, 12, 14} →
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
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21689] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25785 :
    (({0, 3, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 13}, {3, 7, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {0, 7, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25785 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 10, 13, 14} →
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
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25785] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28857 :
    (({0, 3, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 12, 13}, {3, 7, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {0, 7, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28857 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 7, 12, 13, 14} →
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
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28857] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05945 :
    (({0, 3, 4, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 12}, {4, 8, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 8, 9, 12}, {4, 5, 8, 9, 10}, {3, 8, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 8, 10, 12}, {3, 5, 8, 9, 12}, {3, 5, 8, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 8, 10, 12}, {3, 4, 8, 9, 12}, {3, 4, 8, 9, 10}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}, {0, 8, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 8, 9, 12}, {0, 4, 8, 9, 10}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05945 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05945] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10041 :
    (({0, 3, 4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 13}, {4, 8, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 10}, {3, 8, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}, {0, 8, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10041 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10041] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18233 :
    (({0, 3, 4, 5, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 14}, {4, 8, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 9, 14}, {4, 5, 8, 9, 10}, {3, 8, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 8, 10, 14}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 10}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}, {0, 8, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 10}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 3, 9, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 10}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18233 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 10, 14} ∨
        polygon = {4, 8, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 10} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 8, 10, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18233] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13113 :
    (({0, 3, 4, 5, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 12, 13}, {4, 8, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 12}, {3, 8, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 8, 12, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 9}, {0, 8, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}, {0, 3, 9, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 9}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13113 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 8, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 12} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 5, 8, 9, 12} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 9} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13113] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13625 :
    (({0, 3, 4, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 10, 12}, {3, 8, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 8, 12, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 12}, {3, 4, 5, 8, 10}, {0, 8, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13625 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {4, 8, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 5, 8, 10, 12} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13625] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25913 :
    (({0, 3, 4, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 13, 14}, {4, 8, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 10, 13}, {3, 8, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 10, 14}, {3, 5, 8, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 8, 10, 14}, {3, 4, 8, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 10}, {0, 8, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 3, 10, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25913 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 8, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {4, 8, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {3, 8, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 10, 14} ∨
        polygon = {3, 5, 8, 10, 13} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 8, 10, 14} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 10} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 8, 10, 14} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 10} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 10} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25913] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28985 :
    (({0, 3, 4, 5, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 12, 13, 14}, {4, 8, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 12, 14}, {4, 5, 8, 12, 13}, {3, 8, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 12, 14}, {3, 5, 8, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 8, 12, 14}, {3, 4, 8, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 12}, {0, 8, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 12, 14}, {0, 4, 8, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 3, 12, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 12}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28985 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 8, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 8, 12, 13, 14} ∨
        polygon = {4, 8, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 8, 12, 14} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {3, 8, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 12, 14} ∨
        polygon = {3, 5, 8, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 8, 12, 14} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 12} ∨
        polygon = {0, 8, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 8, 12, 14} ∨
        polygon = {0, 4, 8, 12, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 8, 14} ∨
        polygon = {0, 4, 5, 8, 13} ∨
        polygon = {0, 4, 5, 8, 12} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 12, 14} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 8, 14} ∨
        polygon = {0, 3, 5, 8, 13} ∨
        polygon = {0, 3, 5, 8, 12} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28985] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13881 :
    (({0, 3, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {0, 9, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13881 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 9, 10, 12, 13} →
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
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13881] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22073 :
    (({0, 3, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {0, 9, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22073 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 9, 10, 12, 14} →
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
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22073] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26169 :
    (({0, 3, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {0, 9, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26169 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 9, 10, 13, 14} →
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
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26169] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask23097 :
    (({0, 3, 4, 5, 9, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 11, 12, 14}, {4, 9, 11, 12, 14}, {4, 5, 11, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 11, 14}, {4, 5, 9, 11, 12}, {3, 9, 11, 12, 14}, {3, 5, 11, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 11, 14}, {3, 5, 9, 11, 12}, {3, 4, 11, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 11, 14}, {3, 4, 9, 11, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 11, 14}, {3, 4, 5, 11, 12}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 11}, {0, 9, 11, 12, 14}, {0, 5, 11, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 11, 14}, {0, 5, 9, 11, 12}, {0, 4, 11, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 11, 14}, {0, 4, 9, 11, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 11, 14}, {0, 4, 5, 11, 12}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 11}, {0, 3, 11, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 11, 14}, {0, 3, 9, 11, 12}, {0, 3, 5, 12, 14}, {0, 3, 5, 11, 14}, {0, 3, 5, 11, 12}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 11}, {0, 3, 4, 12, 14}, {0, 3, 4, 11, 14}, {0, 3, 4, 11, 12}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 11}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 11}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask23097 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 9, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 11, 12, 14} ∨
        polygon = {4, 9, 11, 12, 14} ∨
        polygon = {4, 5, 11, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 11, 14} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {3, 9, 11, 12, 14} ∨
        polygon = {3, 5, 11, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 11, 14} ∨
        polygon = {3, 5, 9, 11, 12} ∨
        polygon = {3, 4, 11, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 11, 14} ∨
        polygon = {3, 4, 9, 11, 12} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 11, 14} ∨
        polygon = {3, 4, 5, 11, 12} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 11} ∨
        polygon = {0, 9, 11, 12, 14} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 11, 14} ∨
        polygon = {0, 5, 9, 11, 12} ∨
        polygon = {0, 4, 11, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 11, 14} ∨
        polygon = {0, 4, 9, 11, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 11, 14} ∨
        polygon = {0, 4, 5, 11, 12} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 11} ∨
        polygon = {0, 3, 11, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 11, 14} ∨
        polygon = {0, 3, 9, 11, 12} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 11, 14} ∨
        polygon = {0, 3, 5, 11, 12} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 9, 11} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 11, 14} ∨
        polygon = {0, 3, 4, 11, 12} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 11} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 11} ∨
        polygon = {0, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 9, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask23097] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29241 :
    (({0, 3, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {0, 9, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29241 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 9, 12, 13, 14} →
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
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29241] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29753 :
    (({0, 3, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {0, 10, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29753 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 5, 10, 12, 13, 14} →
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
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29753] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05081 :
    (({0, 3, 4, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 12}, {4, 7, 8, 9, 12}, {4, 6, 8, 9, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 9}, {3, 7, 8, 9, 12}, {3, 6, 8, 9, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 9}, {3, 4, 8, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 9}, {3, 4, 6, 9, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}, {0, 7, 8, 9, 12}, {0, 6, 8, 9, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 4, 8, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 3, 8, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05081 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 9} ∨
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
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05081] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09177 :
    (({0, 3, 4, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 13}, {4, 7, 8, 9, 13}, {4, 6, 8, 9, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 9}, {3, 7, 8, 9, 13}, {3, 6, 8, 9, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 9}, {3, 4, 8, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 9}, {3, 4, 6, 9, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 9}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {3, 4, 6, 7, 8}, {0, 7, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 9}, {0, 4, 8, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 3, 8, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 9}, {0, 3, 6, 9, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 3, 4, 9, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09177 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 9} ∨
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
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09177] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05593 :
    (({0, 3, 4, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {4, 7, 8, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 10}, {3, 7, 8, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {3, 4, 8, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 10}, {3, 4, 6, 10, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 10}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 8}, {0, 7, 8, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 4, 8, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 3, 8, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05593 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 8, 12} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
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
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05593] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09689 :
    (({0, 3, 4, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 13}, {4, 7, 8, 10, 13}, {4, 6, 8, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 10}, {3, 7, 8, 10, 13}, {3, 6, 8, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 10}, {3, 4, 8, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 10}, {3, 4, 6, 10, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 10}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 8}, {0, 7, 8, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 4, 8, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 3, 8, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 6, 10, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09689 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 8, 13} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 10} ∨
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
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09689] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05849 :
    (({0, 3, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {0, 7, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05849 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 9, 10, 12} →
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
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
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
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05849] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09945 :
    (({0, 3, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {0, 7, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09945 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 9, 10, 13} →
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
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 10} ∨
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
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09945] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18137 :
    (({0, 3, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {0, 7, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18137 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 9, 10, 14} →
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
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 10} ∨
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
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18137] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13017 :
    (({0, 3, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {3, 7, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {0, 7, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13017 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 9, 12, 13} →
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
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
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
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13017] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21209 :
    (({0, 3, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}, {3, 7, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 4, 9, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {0, 7, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21209 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 12} ∨
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
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21209] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25305 :
    (({0, 3, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {3, 7, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {0, 7, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25305 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
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
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25305] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13529 :
    (({0, 3, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}, {3, 7, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {0, 7, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13529 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
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
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13529] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21721 :
    (({0, 3, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 12}, {3, 7, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {0, 7, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21721 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
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
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21721] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25817 :
    (({0, 3, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}, {3, 7, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {0, 7, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25817 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
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
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25817] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28889 :
    (({0, 3, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}, {3, 7, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {0, 7, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28889 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 12, 13} ∨
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
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28889] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05977 :
    (({0, 3, 4, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 12}, {4, 8, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 8, 9, 12}, {4, 6, 8, 9, 10}, {3, 8, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 8, 9, 12}, {3, 6, 8, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 8, 10, 12}, {3, 4, 8, 9, 12}, {3, 4, 8, 9, 10}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}, {0, 8, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 8, 9, 12}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05977 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 10} ∨
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
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05977] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10073 :
    (({0, 3, 4, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 13}, {4, 8, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 10}, {3, 8, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 10}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}, {0, 8, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10073 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 10} ∨
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
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10073] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18265 :
    (({0, 3, 4, 6, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 14}, {4, 8, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 8, 10, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 10}, {3, 8, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 9, 14}, {3, 6, 8, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 8, 10, 14}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 10}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}, {0, 8, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 3, 9, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 10}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18265 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 8, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {4, 8, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {3, 8, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 8, 10, 14} ∨
        polygon = {3, 6, 8, 9, 14} ∨
        polygon = {3, 6, 8, 9, 10} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 8, 10, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 10} ∨
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
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 8, 10, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 8, 14} ∨
        polygon = {0, 3, 6, 8, 10} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18265] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13145 :
    (({0, 3, 4, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 13}, {4, 8, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 8, 12, 13}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 12}, {3, 8, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 9, 13}, {3, 6, 8, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 8, 12, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 9}, {0, 8, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 3, 9, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13145 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 8, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 8, 12, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 9, 13} ∨
        polygon = {3, 6, 8, 9, 12} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 9} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 12} ∨
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
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 8, 12, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 8, 13} ∨
        polygon = {0, 3, 6, 8, 12} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13145] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13657 :
    (({0, 3, 4, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 8, 12, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 10, 12}, {3, 8, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 8, 12, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 10, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 10}, {0, 8, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 10, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13657 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 3, 4, 6, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {4, 8, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 8, 12, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 8, 12, 13} ∨
        polygon = {3, 6, 8, 10, 13} ∨
        polygon = {3, 6, 8, 10, 12} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 8, 12, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 8, 13} ∨
        polygon = {3, 4, 6, 8, 12} ∨
        polygon = {3, 4, 6, 8, 10} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 12} ∨
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
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 3, 4, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13657] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
