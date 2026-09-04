module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 077. -/

theorem fin15Anchored_fiveFamily_mask21171 :
    (({0, 1, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 12}, {1, 7, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {0, 7, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21171 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 12} ∨
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
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21171] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25267 :
    (({0, 1, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 13}, {1, 7, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {0, 7, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25267 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {4, 5, 7, 9, 13} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25267] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask19635 :
    (({0, 1, 4, 5, 7, 10, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 11, 14}, {4, 7, 10, 11, 14}, {4, 5, 10, 11, 14}, {4, 5, 7, 11, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 11}, {1, 7, 10, 11, 14}, {1, 5, 10, 11, 14}, {1, 5, 7, 11, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 11}, {1, 4, 10, 11, 14}, {1, 4, 7, 11, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 11}, {1, 4, 5, 11, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 11}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 11}, {1, 4, 5, 7, 10}, {0, 7, 10, 11, 14}, {0, 5, 10, 11, 14}, {0, 5, 7, 11, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 11}, {0, 4, 10, 11, 14}, {0, 4, 7, 11, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 11}, {0, 4, 5, 11, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 11}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 11}, {0, 4, 5, 7, 10}, {0, 1, 10, 11, 14}, {0, 1, 7, 11, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 11}, {0, 1, 5, 11, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 11}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 11}, {0, 1, 5, 7, 10}, {0, 1, 4, 11, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 11}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 11}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 11}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask19635 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 10, 11, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 11, 14} ∨
        polygon = {4, 7, 10, 11, 14} ∨
        polygon = {4, 5, 10, 11, 14} ∨
        polygon = {4, 5, 7, 11, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {1, 7, 10, 11, 14} ∨
        polygon = {1, 5, 10, 11, 14} ∨
        polygon = {1, 5, 7, 11, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 10, 11} ∨
        polygon = {1, 4, 10, 11, 14} ∨
        polygon = {1, 4, 7, 11, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 11} ∨
        polygon = {1, 4, 5, 11, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 11} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 11} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {0, 7, 10, 11, 14} ∨
        polygon = {0, 5, 10, 11, 14} ∨
        polygon = {0, 5, 7, 11, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 11} ∨
        polygon = {0, 4, 10, 11, 14} ∨
        polygon = {0, 4, 7, 11, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 11} ∨
        polygon = {0, 4, 5, 11, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 11} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 11} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 1, 10, 11, 14} ∨
        polygon = {0, 1, 7, 11, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 5, 11, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 11} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 11} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 11, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 11} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 10, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask19635] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13491 :
    (({0, 1, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 10, 12}, {1, 7, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {0, 7, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13491 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {4, 5, 7, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13491] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21683 :
    (({0, 1, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 12}, {1, 7, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {0, 7, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21683 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21683] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25779 :
    (({0, 1, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 13}, {1, 7, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {0, 7, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25779 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {4, 5, 7, 10, 13} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25779] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22707 :
    (({0, 1, 4, 5, 7, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 11, 12, 14}, {4, 7, 11, 12, 14}, {4, 5, 11, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 11, 14}, {4, 5, 7, 11, 12}, {1, 7, 11, 12, 14}, {1, 5, 11, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 11, 14}, {1, 5, 7, 11, 12}, {1, 4, 11, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 11, 14}, {1, 4, 7, 11, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 11, 14}, {1, 4, 5, 11, 12}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 11}, {0, 7, 11, 12, 14}, {0, 5, 11, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 11, 14}, {0, 5, 7, 11, 12}, {0, 4, 11, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 11, 14}, {0, 4, 7, 11, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 11, 14}, {0, 4, 5, 11, 12}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 11}, {0, 1, 11, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 11, 14}, {0, 1, 7, 11, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 11, 14}, {0, 1, 5, 11, 12}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 11}, {0, 1, 4, 12, 14}, {0, 1, 4, 11, 14}, {0, 1, 4, 11, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 11}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 11}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22707 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 11, 12, 14} ∨
        polygon = {4, 7, 11, 12, 14} ∨
        polygon = {4, 5, 11, 12, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 11, 14} ∨
        polygon = {4, 5, 7, 11, 12} ∨
        polygon = {1, 7, 11, 12, 14} ∨
        polygon = {1, 5, 11, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 11, 14} ∨
        polygon = {1, 5, 7, 11, 12} ∨
        polygon = {1, 4, 11, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 11, 14} ∨
        polygon = {1, 4, 7, 11, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 11, 14} ∨
        polygon = {1, 4, 5, 11, 12} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 11} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 11, 14} ∨
        polygon = {0, 5, 7, 11, 12} ∨
        polygon = {0, 4, 11, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 11, 14} ∨
        polygon = {0, 4, 7, 11, 12} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 11, 14} ∨
        polygon = {0, 4, 5, 11, 12} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 11} ∨
        polygon = {0, 1, 11, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 11, 14} ∨
        polygon = {0, 1, 7, 11, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 11, 14} ∨
        polygon = {0, 1, 5, 11, 12} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 11} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 11, 14} ∨
        polygon = {0, 1, 4, 11, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 11} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22707] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28851 :
    (({0, 1, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 12, 13}, {1, 7, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {0, 7, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28851 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {4, 5, 7, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28851] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10035 :
    (({0, 1, 4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 13}, {4, 8, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 10}, {1, 8, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 8, 10, 13}, {1, 5, 8, 9, 13}, {1, 5, 8, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 8, 9, 13}, {1, 4, 8, 9, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 10}, {1, 4, 5, 8, 9}, {0, 8, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 10}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}, {0, 1, 9, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 9, 13}, {0, 1, 8, 9, 10}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 10}, {0, 1, 5, 8, 9}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10035 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {4, 5, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 13} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 5, 8, 9, 13} ∨
        polygon = {1, 5, 8, 9, 10} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 10} ∨
        polygon = {1, 4, 5, 8, 9} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10035] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13619 :
    (({0, 1, 4, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 10, 12}, {1, 8, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 8, 12, 13}, {1, 5, 8, 10, 13}, {1, 5, 8, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 8, 12, 13}, {1, 4, 8, 10, 13}, {1, 4, 8, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 12}, {1, 4, 5, 8, 10}, {0, 8, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}, {0, 1, 10, 12, 13}, {0, 1, 8, 12, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 12}, {0, 1, 5, 8, 10}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13619 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 8, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {4, 8, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 8, 12, 13} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {4, 5, 8, 10, 12} ∨
        polygon = {1, 8, 10, 12, 13} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 5, 8, 12, 13} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 5, 8, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 8, 12, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 12} ∨
        polygon = {1, 4, 5, 8, 10} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 8, 12, 13} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 12} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13619] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25907 :
    (({0, 1, 4, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 13, 14}, {4, 8, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 10, 13}, {1, 8, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 8, 13, 14}, {1, 5, 8, 10, 14}, {1, 5, 8, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 8, 10, 14}, {1, 4, 8, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 10}, {0, 8, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 10}, {0, 1, 10, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 10, 14}, {0, 1, 8, 10, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 8, 14}, {0, 1, 5, 8, 13}, {0, 1, 5, 8, 10}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25907 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 8, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 8, 10, 13, 14} ∨
        polygon = {4, 8, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 8, 10, 14} ∨
        polygon = {4, 5, 8, 10, 13} ∨
        polygon = {1, 8, 10, 13, 14} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 5, 8, 13, 14} ∨
        polygon = {1, 5, 8, 10, 14} ∨
        polygon = {1, 5, 8, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 8, 10, 14} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 10} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 8, 10, 14} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 8, 14} ∨
        polygon = {0, 1, 5, 8, 13} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25907] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13875 :
    (({0, 1, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {0, 9, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13875 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {4, 5, 9, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13875] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22067 :
    (({0, 1, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {0, 9, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22067 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22067] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26163 :
    (({0, 1, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {0, 9, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26163 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {4, 5, 9, 10, 13} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26163] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask23091 :
    (({0, 1, 4, 5, 9, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 11, 12, 14}, {4, 9, 11, 12, 14}, {4, 5, 11, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 11, 14}, {4, 5, 9, 11, 12}, {1, 9, 11, 12, 14}, {1, 5, 11, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 11, 14}, {1, 5, 9, 11, 12}, {1, 4, 11, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 11, 14}, {1, 4, 9, 11, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 11, 14}, {1, 4, 5, 11, 12}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 11}, {0, 9, 11, 12, 14}, {0, 5, 11, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 11, 14}, {0, 5, 9, 11, 12}, {0, 4, 11, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 11, 14}, {0, 4, 9, 11, 12}, {0, 4, 5, 12, 14}, {0, 4, 5, 11, 14}, {0, 4, 5, 11, 12}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 11}, {0, 1, 11, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 11, 14}, {0, 1, 9, 11, 12}, {0, 1, 5, 12, 14}, {0, 1, 5, 11, 14}, {0, 1, 5, 11, 12}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 11}, {0, 1, 4, 12, 14}, {0, 1, 4, 11, 14}, {0, 1, 4, 11, 12}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 11}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 11}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask23091 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 9, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 11, 12, 14} ∨
        polygon = {4, 9, 11, 12, 14} ∨
        polygon = {4, 5, 11, 12, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 11, 14} ∨
        polygon = {4, 5, 9, 11, 12} ∨
        polygon = {1, 9, 11, 12, 14} ∨
        polygon = {1, 5, 11, 12, 14} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 9, 11, 14} ∨
        polygon = {1, 5, 9, 11, 12} ∨
        polygon = {1, 4, 11, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 11, 14} ∨
        polygon = {1, 4, 9, 11, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 11, 14} ∨
        polygon = {1, 4, 5, 11, 12} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 11} ∨
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
        polygon = {0, 1, 11, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 11, 14} ∨
        polygon = {0, 1, 9, 11, 12} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 11, 14} ∨
        polygon = {0, 1, 5, 11, 12} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 11} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 11, 14} ∨
        polygon = {0, 1, 4, 11, 12} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 11} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 11} ∨
        polygon = {0, 1, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 9, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask23091] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29235 :
    (({0, 1, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {0, 9, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29235 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {4, 5, 9, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29235] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29747 :
    (({0, 1, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 10, 12, 14}, {1, 5, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {0, 10, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29747 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 5, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {4, 5, 10, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29747] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask02003 :
    (({0, 1, 4, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 10}, {4, 7, 8, 9, 10}, {4, 6, 8, 9, 10}, {4, 6, 7, 9, 10}, {4, 6, 7, 8, 10}, {4, 6, 7, 8, 9}, {1, 7, 8, 9, 10}, {1, 6, 8, 9, 10}, {1, 6, 7, 9, 10}, {1, 6, 7, 8, 10}, {1, 6, 7, 8, 9}, {1, 4, 8, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 7, 8, 10}, {1, 4, 7, 8, 9}, {1, 4, 6, 9, 10}, {1, 4, 6, 8, 10}, {1, 4, 6, 8, 9}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 4, 6, 7, 8}, {0, 7, 8, 9, 10}, {0, 6, 8, 9, 10}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 4, 8, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 1, 8, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}, {0, 1, 6, 9, 10}, {0, 1, 6, 8, 10}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask02003 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 10} ∨
        polygon = {1, 6, 8, 9, 10} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 6, 8, 9, 10} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} ∨
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
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask02003] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05075 :
    (({0, 1, 4, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 12}, {4, 7, 8, 9, 12}, {4, 6, 8, 9, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 9}, {1, 7, 8, 9, 12}, {1, 6, 8, 9, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 8, 12}, {1, 6, 7, 8, 9}, {1, 4, 8, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 8, 12}, {1, 4, 7, 8, 9}, {1, 4, 6, 9, 12}, {1, 4, 6, 8, 12}, {1, 4, 6, 8, 9}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 4, 6, 7, 8}, {0, 7, 8, 9, 12}, {0, 6, 8, 9, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 4, 8, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 1, 8, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 9}, {0, 1, 6, 9, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 4, 9, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05075 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 12} ∨
        polygon = {1, 6, 8, 9, 12} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 6, 7, 8, 12} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 8, 12} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 8, 12} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 6, 7, 8} ∨
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
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05075] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09171 :
    (({0, 1, 4, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 13}, {4, 7, 8, 9, 13}, {4, 6, 8, 9, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 9}, {1, 7, 8, 9, 13}, {1, 6, 8, 9, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 8, 13}, {1, 6, 7, 8, 9}, {1, 4, 8, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 8, 13}, {1, 4, 7, 8, 9}, {1, 4, 6, 9, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 9}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 4, 6, 7, 8}, {0, 7, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 9}, {0, 4, 8, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 9}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}, {0, 1, 8, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 9}, {0, 1, 6, 9, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 4, 9, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09171 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 13} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 8, 13} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 6, 7, 8} ∨
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
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09171] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05587 :
    (({0, 1, 4, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {4, 7, 8, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 10}, {1, 7, 8, 10, 12}, {1, 6, 8, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 8, 12}, {1, 6, 7, 8, 10}, {1, 4, 8, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 8, 12}, {1, 4, 7, 8, 10}, {1, 4, 6, 10, 12}, {1, 4, 6, 8, 12}, {1, 4, 6, 8, 10}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 8}, {0, 7, 8, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 4, 8, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 1, 8, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 10}, {0, 1, 6, 10, 12}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 10}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 8}, {0, 1, 4, 10, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05587 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 12} ∨
        polygon = {1, 6, 8, 10, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 8, 12} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 8, 12} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 8, 12} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 8} ∨
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
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05587] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09683 :
    (({0, 1, 4, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 13}, {4, 7, 8, 10, 13}, {4, 6, 8, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 8, 13}, {4, 6, 7, 8, 10}, {1, 7, 8, 10, 13}, {1, 6, 8, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 8, 13}, {1, 6, 7, 8, 10}, {1, 4, 8, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 8, 13}, {1, 4, 7, 8, 10}, {1, 4, 6, 10, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 10}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 8}, {0, 7, 8, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 4, 8, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 1, 8, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 10}, {0, 1, 6, 10, 13}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 10}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 8}, {0, 1, 4, 10, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09683 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 13} ∨
        polygon = {1, 6, 8, 10, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 8, 13} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 8} ∨
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
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09683] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17875 :
    (({0, 1, 4, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 14}, {4, 7, 8, 10, 14}, {4, 6, 8, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 10}, {1, 7, 8, 10, 14}, {1, 6, 8, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 8, 14}, {1, 6, 7, 8, 10}, {1, 4, 8, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 10}, {1, 4, 6, 10, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 8, 10}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 8}, {0, 7, 8, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 10}, {0, 4, 8, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 10}, {0, 4, 6, 10, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}, {0, 1, 8, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 10}, {0, 1, 6, 10, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 10}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 8}, {0, 1, 4, 10, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17875 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {4, 7, 8, 10, 14} ∨
        polygon = {4, 6, 8, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 14} ∨
        polygon = {1, 6, 8, 10, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 4, 8, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 10} ∨
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
        polygon = {0, 1, 8, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17875] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20947 :
    (({0, 1, 4, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 12, 14}, {4, 7, 8, 12, 14}, {4, 6, 8, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 12}, {1, 7, 8, 12, 14}, {1, 6, 8, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 8, 14}, {1, 6, 7, 8, 12}, {1, 4, 8, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 8, 12}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 8}, {0, 7, 8, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 4, 8, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 8}, {0, 1, 8, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 12}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 8}, {0, 1, 4, 12, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20947 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {4, 7, 8, 12, 14} ∨
        polygon = {4, 6, 8, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 12} ∨
        polygon = {1, 7, 8, 12, 14} ∨
        polygon = {1, 6, 8, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 6, 7, 8, 12} ∨
        polygon = {1, 4, 8, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 12} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 8, 12} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 12} ∨
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
        polygon = {0, 1, 8, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20947] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25043 :
    (({0, 1, 4, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 13, 14}, {4, 7, 8, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 13}, {1, 7, 8, 13, 14}, {1, 6, 8, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 8, 14}, {1, 6, 7, 8, 13}, {1, 4, 8, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 8, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 8}, {0, 7, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}, {0, 4, 8, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 8}, {0, 1, 8, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 8}, {0, 1, 4, 13, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 8}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 8}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25043 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {4, 7, 8, 13, 14} ∨
        polygon = {4, 6, 8, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {4, 6, 7, 8, 13} ∨
        polygon = {1, 7, 8, 13, 14} ∨
        polygon = {1, 6, 8, 13, 14} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 6, 7, 8, 13} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 13} ∨
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
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 8} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25043] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05843 :
    (({0, 1, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {0, 7, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05843 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {4, 6, 7, 9, 10} ∨
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
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05843] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09939 :
    (({0, 1, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {0, 7, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09939 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 10} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09939] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18131 :
    (({0, 1, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {0, 7, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18131 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 10} ∨
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
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18131] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13011 :
    (({0, 1, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {0, 7, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13011 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {4, 6, 7, 9, 12} ∨
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
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13011] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21203 :
    (({0, 1, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {0, 7, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21203 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 12} ∨
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
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21203] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25299 :
    (({0, 1, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {1, 7, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {0, 7, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25299 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {4, 6, 7, 9, 13} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25299] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask07379 :
    (({0, 1, 4, 6, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 11, 12}, {4, 7, 10, 11, 12}, {4, 6, 10, 11, 12}, {4, 6, 7, 11, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 10, 11}, {1, 7, 10, 11, 12}, {1, 6, 10, 11, 12}, {1, 6, 7, 11, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 10, 11}, {1, 4, 10, 11, 12}, {1, 4, 7, 11, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 10, 11}, {1, 4, 6, 11, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 10, 11}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 11}, {1, 4, 6, 7, 10}, {0, 7, 10, 11, 12}, {0, 6, 10, 11, 12}, {0, 6, 7, 11, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 10, 11}, {0, 4, 10, 11, 12}, {0, 4, 7, 11, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 10, 11}, {0, 4, 6, 11, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 10, 11}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 11}, {0, 4, 6, 7, 10}, {0, 1, 10, 11, 12}, {0, 1, 7, 11, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 10, 11}, {0, 1, 6, 11, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 10, 11}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 11}, {0, 1, 6, 7, 10}, {0, 1, 4, 11, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 10, 11}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 11}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 11}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07379 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 11, 12} ∨
        polygon = {4, 7, 10, 11, 12} ∨
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {4, 6, 7, 10, 11} ∨
        polygon = {1, 7, 10, 11, 12} ∨
        polygon = {1, 6, 10, 11, 12} ∨
        polygon = {1, 6, 7, 11, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 10, 11} ∨
        polygon = {1, 4, 10, 11, 12} ∨
        polygon = {1, 4, 7, 11, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 10, 11} ∨
        polygon = {1, 4, 6, 11, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 10, 11} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 11} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 6, 10, 11, 12} ∨
        polygon = {0, 6, 7, 11, 12} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 11} ∨
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
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 7, 11, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 6, 11, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 10, 11} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 11} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 11, 12} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 11} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07379] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13523 :
    (({0, 1, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}, {1, 7, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {0, 7, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13523 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 7, 12, 13} ∨
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {4, 6, 7, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13523] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21715 :
    (({0, 1, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 12}, {1, 7, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {0, 7, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21715 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 12} ∨
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
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21715] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25811 :
    (({0, 1, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}, {1, 7, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {0, 7, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25811 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {4, 6, 7, 10, 13} ∨
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
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25811] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28883 :
    (({0, 1, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}, {1, 7, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {0, 7, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28883 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 7, 13, 14} ∨
        polygon = {4, 6, 7, 12, 14} ∨
        polygon = {4, 6, 7, 12, 13} ∨
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
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28883] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05971 :
    (({0, 1, 4, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 12}, {4, 8, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 8, 9, 12}, {4, 6, 8, 9, 10}, {1, 8, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 8, 10, 12}, {1, 6, 8, 9, 12}, {1, 6, 8, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 8, 10, 12}, {1, 4, 8, 9, 12}, {1, 4, 8, 9, 10}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 4, 6, 8, 12}, {1, 4, 6, 8, 10}, {1, 4, 6, 8, 9}, {0, 8, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 4, 9, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 8, 9, 12}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 1, 9, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 8, 9, 12}, {0, 1, 8, 9, 10}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 10}, {0, 1, 6, 8, 9}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05971 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {4, 6, 8, 10, 12} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 12} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 6, 8, 10, 12} ∨
        polygon = {1, 6, 8, 9, 12} ∨
        polygon = {1, 6, 8, 9, 10} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 8, 12} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 6, 8, 9} ∨
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
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05971] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10067 :
    (({0, 1, 4, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 13}, {4, 8, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 10}, {1, 8, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 8, 10, 13}, {1, 6, 8, 9, 13}, {1, 6, 8, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 8, 9, 13}, {1, 4, 8, 9, 10}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 10}, {1, 4, 6, 8, 9}, {0, 8, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 4, 9, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 10}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}, {0, 1, 9, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 9, 13}, {0, 1, 8, 9, 10}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 10}, {0, 1, 6, 8, 9}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10067 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 8, 10, 13} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {4, 6, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 8, 10, 13} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 6, 8, 9, 10} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 8, 10} ∨
        polygon = {1, 4, 6, 8, 9} ∨
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
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10067] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21331 :
    (({0, 1, 4, 6, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 14}, {4, 8, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 8, 12, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 12}, {1, 8, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 8, 12, 14}, {1, 6, 8, 9, 14}, {1, 6, 8, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 8, 12, 14}, {1, 4, 8, 9, 14}, {1, 4, 8, 9, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 6, 8, 14}, {1, 4, 6, 8, 12}, {1, 4, 6, 8, 9}, {0, 8, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 12}, {0, 4, 9, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 12}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}, {0, 1, 9, 12, 14}, {0, 1, 8, 12, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 12}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 12}, {0, 1, 6, 8, 9}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21331 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 8, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {4, 8, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 8, 12, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 12} ∨
        polygon = {1, 8, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 8, 12, 14} ∨
        polygon = {1, 6, 8, 9, 14} ∨
        polygon = {1, 6, 8, 9, 12} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 8, 12, 14} ∨
        polygon = {1, 4, 8, 9, 14} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 8, 12} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 8, 12, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 8, 14} ∨
        polygon = {0, 4, 6, 8, 12} ∨
        polygon = {0, 4, 6, 8, 9} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 8, 12, 14} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 12} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21331] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25427 :
    (({0, 1, 4, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 13, 14}, {4, 8, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 8, 9, 14}, {4, 6, 8, 9, 13}, {1, 8, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 8, 13, 14}, {1, 6, 8, 9, 14}, {1, 6, 8, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 8, 9, 14}, {1, 4, 8, 9, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 8, 14}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 9}, {0, 8, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 4, 9, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 13}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}, {0, 1, 9, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 13}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 6, 8, 14}, {0, 1, 6, 8, 13}, {0, 1, 6, 8, 9}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25427 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 4, 6, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {4, 8, 9, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 8, 13, 14} ∨
        polygon = {4, 6, 8, 9, 14} ∨
        polygon = {4, 6, 8, 9, 13} ∨
        polygon = {1, 8, 9, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 8, 13, 14} ∨
        polygon = {1, 6, 8, 9, 14} ∨
        polygon = {1, 6, 8, 9, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 8, 9, 14} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 8, 13} ∨
        polygon = {1, 4, 6, 8, 9} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 13} ∨
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
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 8, 14} ∨
        polygon = {0, 1, 6, 8, 13} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 4, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25427] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
