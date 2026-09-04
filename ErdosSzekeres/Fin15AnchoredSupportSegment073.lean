module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 073. -/

theorem fin15Anchored_fiveFamily_mask21083 :
    (({0, 1, 3, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {1, 6, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {0, 6, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 1, 9, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21083 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
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
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21083] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25179 :
    (({0, 1, 3, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {1, 6, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}, {0, 6, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 1, 9, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25179 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25179] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask07259 :
    (({0, 1, 3, 4, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 11, 12}, {3, 6, 10, 11, 12}, {3, 4, 10, 11, 12}, {3, 4, 6, 11, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 10, 11}, {1, 6, 10, 11, 12}, {1, 4, 10, 11, 12}, {1, 4, 6, 11, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 10, 11}, {1, 3, 10, 11, 12}, {1, 3, 6, 11, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 10, 11}, {1, 3, 4, 11, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 10, 11}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 11}, {1, 3, 4, 6, 10}, {0, 6, 10, 11, 12}, {0, 4, 10, 11, 12}, {0, 4, 6, 11, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 10, 11}, {0, 3, 10, 11, 12}, {0, 3, 6, 11, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 10, 11}, {0, 3, 4, 11, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 10, 11}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 11}, {0, 3, 4, 6, 10}, {0, 1, 10, 11, 12}, {0, 1, 6, 11, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 10, 11}, {0, 1, 4, 11, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 10, 11}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 11}, {0, 1, 4, 6, 10}, {0, 1, 3, 11, 12}, {0, 1, 3, 10, 12}, {0, 1, 3, 10, 11}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 11}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 11}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask07259 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 10, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 11, 12} ∨
        polygon = {3, 6, 10, 11, 12} ∨
        polygon = {3, 4, 10, 11, 12} ∨
        polygon = {3, 4, 6, 11, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 10, 11} ∨
        polygon = {1, 6, 10, 11, 12} ∨
        polygon = {1, 4, 10, 11, 12} ∨
        polygon = {1, 4, 6, 11, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 10, 11} ∨
        polygon = {1, 3, 10, 11, 12} ∨
        polygon = {1, 3, 6, 11, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 10, 11} ∨
        polygon = {1, 3, 4, 11, 12} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 10, 11} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 11} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {0, 6, 10, 11, 12} ∨
        polygon = {0, 4, 10, 11, 12} ∨
        polygon = {0, 4, 6, 11, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 10, 11} ∨
        polygon = {0, 3, 10, 11, 12} ∨
        polygon = {0, 3, 6, 11, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 10, 11} ∨
        polygon = {0, 3, 4, 11, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 10, 11} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 11} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 1, 10, 11, 12} ∨
        polygon = {0, 1, 6, 11, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 10, 11} ∨
        polygon = {0, 1, 4, 11, 12} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 11} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 3, 11, 12} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 11} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 11} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask07259] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13403 :
    (({0, 1, 3, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {1, 6, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {0, 6, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 1, 10, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13403 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
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
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13403] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21595 :
    (({0, 1, 3, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {1, 6, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {0, 6, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 1, 10, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21595 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
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
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21595] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25691 :
    (({0, 1, 3, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {1, 6, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {0, 6, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 1, 10, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25691 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25691] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28763 :
    (({0, 1, 3, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {1, 6, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {0, 6, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 1, 12, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28763 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28763] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01947 :
    (({0, 1, 3, 4, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 10}, {3, 7, 8, 9, 10}, {3, 4, 8, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 7, 8, 10}, {3, 4, 7, 8, 9}, {1, 7, 8, 9, 10}, {1, 4, 8, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 7, 8, 10}, {1, 4, 7, 8, 9}, {1, 3, 8, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 7, 8, 10}, {1, 3, 7, 8, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 8, 10}, {1, 3, 4, 8, 9}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 7, 8}, {0, 7, 8, 9, 10}, {0, 4, 8, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 7, 8, 10}, {0, 4, 7, 8, 9}, {0, 3, 8, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 1, 8, 9, 10}, {0, 1, 7, 9, 10}, {0, 1, 7, 8, 10}, {0, 1, 7, 8, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01947 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 8, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 7, 8, 9, 10} ∨
        polygon = {3, 7, 8, 9, 10} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 10} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {0, 7, 8, 9, 10} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01947] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05019 :
    (({0, 1, 3, 4, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 12}, {3, 7, 8, 9, 12}, {3, 4, 8, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 9}, {1, 7, 8, 9, 12}, {1, 4, 8, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 8, 12}, {1, 4, 7, 8, 9}, {1, 3, 8, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 9}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 3, 4, 7, 8}, {0, 7, 8, 9, 12}, {0, 4, 8, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}, {0, 3, 8, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 1, 8, 9, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 3, 9, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05019 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 8, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 7, 8, 9, 12} ∨
        polygon = {3, 7, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 12} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 8, 12} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05019] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09115 :
    (({0, 1, 3, 4, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 13}, {3, 7, 8, 9, 13}, {3, 4, 8, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 9}, {1, 7, 8, 9, 13}, {1, 4, 8, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 8, 13}, {1, 4, 7, 8, 9}, {1, 3, 8, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 9}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 3, 4, 7, 8}, {0, 7, 8, 9, 13}, {0, 4, 8, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 9}, {0, 3, 8, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 9}, {0, 3, 4, 9, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}, {0, 1, 8, 9, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 9}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 7, 8}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09115 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 8, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 8, 9, 13} ∨
        polygon = {3, 7, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 9} ∨
        polygon = {1, 7, 8, 9, 13} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 7, 8, 9} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 9} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09115] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05531 :
    (({0, 1, 3, 4, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 10, 12}, {3, 7, 8, 10, 12}, {3, 4, 8, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 10}, {1, 7, 8, 10, 12}, {1, 4, 8, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 8, 12}, {1, 4, 7, 8, 10}, {1, 3, 8, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 10}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 8}, {0, 7, 8, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}, {0, 3, 8, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 1, 8, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 8, 12}, {0, 1, 7, 8, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 3, 10, 12}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05531 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 8, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 7, 8, 10, 12} ∨
        polygon = {3, 7, 8, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 8, 12} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 12} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 8, 12} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 8, 12} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 8, 12} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 8, 12} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05531] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09627 :
    (({0, 1, 3, 4, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 10, 13}, {3, 7, 8, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 10}, {1, 7, 8, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 8, 13}, {1, 4, 7, 8, 10}, {1, 3, 8, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 10}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 8}, {0, 7, 8, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}, {0, 3, 8, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}, {0, 1, 8, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 8, 13}, {0, 1, 7, 8, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 8}, {0, 1, 3, 10, 13}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09627 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 8, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 8, 10, 13} ∨
        polygon = {3, 7, 8, 10, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {3, 4, 7, 8, 10} ∨
        polygon = {1, 7, 8, 10, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 4, 7, 8, 10} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 4, 7, 8, 10} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 7, 8, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09627] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24987 :
    (({0, 1, 3, 4, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 13, 14}, {3, 7, 8, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 13}, {1, 7, 8, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 13}, {1, 3, 8, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 8}, {0, 7, 8, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 13}, {0, 3, 8, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 8}, {0, 1, 8, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 8, 14}, {0, 1, 7, 8, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 8}, {0, 1, 3, 13, 14}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 8}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 8}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24987 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 8, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 8, 13, 14} ∨
        polygon = {3, 7, 8, 13, 14} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 13} ∨
        polygon = {1, 7, 8, 13, 14} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 13} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 7, 8, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 8, 14} ∨
        polygon = {0, 4, 7, 8, 13} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 8, 14} ∨
        polygon = {0, 3, 7, 8, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 8} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 8, 14} ∨
        polygon = {0, 1, 7, 8, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 8} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 8} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24987] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask03739 :
    (({0, 1, 3, 4, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 11}, {3, 7, 9, 10, 11}, {3, 4, 9, 10, 11}, {3, 4, 7, 10, 11}, {3, 4, 7, 9, 11}, {3, 4, 7, 9, 10}, {1, 7, 9, 10, 11}, {1, 4, 9, 10, 11}, {1, 4, 7, 10, 11}, {1, 4, 7, 9, 11}, {1, 4, 7, 9, 10}, {1, 3, 9, 10, 11}, {1, 3, 7, 10, 11}, {1, 3, 7, 9, 11}, {1, 3, 7, 9, 10}, {1, 3, 4, 10, 11}, {1, 3, 4, 9, 11}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 11}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {0, 7, 9, 10, 11}, {0, 4, 9, 10, 11}, {0, 4, 7, 10, 11}, {0, 4, 7, 9, 11}, {0, 4, 7, 9, 10}, {0, 3, 9, 10, 11}, {0, 3, 7, 10, 11}, {0, 3, 7, 9, 11}, {0, 3, 7, 9, 10}, {0, 3, 4, 10, 11}, {0, 3, 4, 9, 11}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 11}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 1, 9, 10, 11}, {0, 1, 7, 10, 11}, {0, 1, 7, 9, 11}, {0, 1, 7, 9, 10}, {0, 1, 4, 10, 11}, {0, 1, 4, 9, 11}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 11}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 3, 10, 11}, {0, 1, 3, 9, 11}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 11}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 11}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask03739 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 9, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 11} ∨
        polygon = {3, 7, 9, 10, 11} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {3, 4, 7, 10, 11} ∨
        polygon = {3, 4, 7, 9, 11} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 11} ∨
        polygon = {1, 4, 9, 10, 11} ∨
        polygon = {1, 4, 7, 10, 11} ∨
        polygon = {1, 4, 7, 9, 11} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 11} ∨
        polygon = {1, 3, 7, 10, 11} ∨
        polygon = {1, 3, 7, 9, 11} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 4, 10, 11} ∨
        polygon = {1, 3, 4, 9, 11} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 11} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 11} ∨
        polygon = {0, 4, 9, 10, 11} ∨
        polygon = {0, 4, 7, 10, 11} ∨
        polygon = {0, 4, 7, 9, 11} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 3, 7, 10, 11} ∨
        polygon = {0, 3, 7, 9, 11} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 10, 11} ∨
        polygon = {0, 3, 4, 9, 11} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 11} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 1, 9, 10, 11} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 7, 9, 11} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 9, 11} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 9, 11} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 11} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 11} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask03739] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05787 :
    (({0, 1, 3, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {1, 7, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {0, 7, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05787 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
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
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05787] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09883 :
    (({0, 1, 3, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {1, 7, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {0, 7, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09883 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
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
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09883] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18075 :
    (({0, 1, 3, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {1, 7, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {0, 7, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18075 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
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
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18075] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12955 :
    (({0, 1, 3, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {1, 7, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {0, 7, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12955 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
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
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12955] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21147 :
    (({0, 1, 3, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {1, 7, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {0, 7, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21147 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
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
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21147] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25243 :
    (({0, 1, 3, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {1, 7, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {0, 7, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25243 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25243] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13467 :
    (({0, 1, 3, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {1, 7, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {0, 7, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13467 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
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
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13467] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21659 :
    (({0, 1, 3, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {1, 7, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {0, 7, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21659 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
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
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21659] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25755 :
    (({0, 1, 3, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {1, 7, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {0, 7, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25755 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25755] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28827 :
    (({0, 1, 3, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {1, 7, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {0, 7, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28827 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28827] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05915 :
    (({0, 1, 3, 4, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 10, 12}, {3, 8, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 8, 10, 12}, {3, 4, 8, 9, 12}, {3, 4, 8, 9, 10}, {1, 8, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 8, 10, 12}, {1, 4, 8, 9, 12}, {1, 4, 8, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 8, 10, 12}, {1, 3, 8, 9, 12}, {1, 3, 8, 9, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 10}, {1, 3, 4, 8, 9}, {0, 8, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 8, 9, 12}, {0, 4, 8, 9, 10}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 1, 9, 10, 12}, {0, 1, 8, 10, 12}, {0, 1, 8, 9, 12}, {0, 1, 8, 9, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 12}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 12}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05915 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {3, 8, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 8, 10, 12} ∨
        polygon = {3, 4, 8, 9, 12} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {0, 8, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 8, 10, 12} ∨
        polygon = {0, 4, 8, 9, 12} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 8, 10, 12} ∨
        polygon = {0, 3, 8, 9, 12} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 12} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 8, 10, 12} ∨
        polygon = {0, 1, 8, 9, 12} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 12} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 12} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05915] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10011 :
    (({0, 1, 3, 4, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 10, 13}, {3, 8, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 10}, {1, 8, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 8, 9, 13}, {1, 4, 8, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 10}, {1, 3, 4, 8, 9}, {0, 8, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 10}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}, {0, 1, 9, 10, 13}, {0, 1, 8, 10, 13}, {0, 1, 8, 9, 13}, {0, 1, 8, 9, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 10}, {0, 1, 4, 8, 9}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 10}, {0, 1, 3, 8, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10011 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 8, 10, 13} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 8, 9, 10} ∨
        polygon = {1, 8, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 8, 10, 13} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 4, 8, 9, 10} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 8, 10, 13} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 8, 9, 10} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 10} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 8, 10, 13} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 8, 9, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 10} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10011] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25371 :
    (({0, 1, 3, 4, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 13, 14}, {3, 8, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 13}, {1, 8, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 8, 9, 14}, {1, 4, 8, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 8, 9, 14}, {1, 3, 8, 9, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 9}, {0, 8, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 13}, {0, 3, 9, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 9}, {0, 1, 9, 13, 14}, {0, 1, 8, 13, 14}, {0, 1, 8, 9, 14}, {0, 1, 8, 9, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 8, 14}, {0, 1, 4, 8, 13}, {0, 1, 4, 8, 9}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 8, 14}, {0, 1, 3, 8, 13}, {0, 1, 3, 8, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25371 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 8, 9, 13, 14} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {1, 8, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 8, 9, 14} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 8, 13, 14} ∨
        polygon = {0, 4, 8, 9, 14} ∨
        polygon = {0, 4, 8, 9, 13} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 8, 13, 14} ∨
        polygon = {0, 3, 8, 9, 14} ∨
        polygon = {0, 3, 8, 9, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 8, 14} ∨
        polygon = {0, 3, 4, 8, 13} ∨
        polygon = {0, 3, 4, 8, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 8, 13, 14} ∨
        polygon = {0, 1, 8, 9, 14} ∨
        polygon = {0, 1, 8, 9, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 8, 14} ∨
        polygon = {0, 1, 4, 8, 13} ∨
        polygon = {0, 1, 4, 8, 9} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 8, 14} ∨
        polygon = {0, 1, 3, 8, 13} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25371] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask11803 :
    (({0, 1, 3, 4, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 11, 13}, {3, 9, 10, 11, 13}, {3, 4, 10, 11, 13}, {3, 4, 9, 11, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 11}, {1, 9, 10, 11, 13}, {1, 4, 10, 11, 13}, {1, 4, 9, 11, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 11}, {1, 3, 10, 11, 13}, {1, 3, 9, 11, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 11}, {1, 3, 4, 11, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 11}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 11}, {1, 3, 4, 9, 10}, {0, 9, 10, 11, 13}, {0, 4, 10, 11, 13}, {0, 4, 9, 11, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 11}, {0, 3, 10, 11, 13}, {0, 3, 9, 11, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 11}, {0, 3, 4, 11, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 11}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 11}, {0, 3, 4, 9, 10}, {0, 1, 10, 11, 13}, {0, 1, 9, 11, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 11}, {0, 1, 4, 11, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 11}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 11}, {0, 1, 4, 9, 10}, {0, 1, 3, 11, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 11}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 11}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 11}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask11803 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 9, 10, 11, 13} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 11, 13} ∨
        polygon = {3, 9, 10, 11, 13} ∨
        polygon = {3, 4, 10, 11, 13} ∨
        polygon = {3, 4, 9, 11, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 11} ∨
        polygon = {1, 9, 10, 11, 13} ∨
        polygon = {1, 4, 10, 11, 13} ∨
        polygon = {1, 4, 9, 11, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 11} ∨
        polygon = {1, 3, 10, 11, 13} ∨
        polygon = {1, 3, 9, 11, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 11} ∨
        polygon = {1, 3, 4, 11, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 11} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 11} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 4, 10, 11, 13} ∨
        polygon = {0, 4, 9, 11, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 11} ∨
        polygon = {0, 3, 10, 11, 13} ∨
        polygon = {0, 3, 9, 11, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 11} ∨
        polygon = {0, 3, 4, 11, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 11} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 11} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 1, 10, 11, 13} ∨
        polygon = {0, 1, 9, 11, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 11} ∨
        polygon = {0, 1, 4, 11, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 11} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 3, 11, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 11} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 11} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 11} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 9, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask11803] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13851 :
    (({0, 1, 3, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {0, 9, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13851 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
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
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13851] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22043 :
    (({0, 1, 3, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {0, 9, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 12}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22043 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
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
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22043] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26139 :
    (({0, 1, 3, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {0, 9, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26139 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26139] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29211 :
    (({0, 1, 3, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {0, 9, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29211 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29211] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29723 :
    (({0, 1, 3, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {0, 10, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29723 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 4, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
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
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29723] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01003 :
    (({0, 1, 3, 5, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 8, 9}, {3, 6, 7, 8, 9}, {3, 5, 7, 8, 9}, {3, 5, 6, 8, 9}, {3, 5, 6, 7, 9}, {3, 5, 6, 7, 8}, {1, 6, 7, 8, 9}, {1, 5, 7, 8, 9}, {1, 5, 6, 8, 9}, {1, 5, 6, 7, 9}, {1, 5, 6, 7, 8}, {1, 3, 7, 8, 9}, {1, 3, 6, 8, 9}, {1, 3, 6, 7, 9}, {1, 3, 6, 7, 8}, {1, 3, 5, 8, 9}, {1, 3, 5, 7, 9}, {1, 3, 5, 7, 8}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 8}, {1, 3, 5, 6, 7}, {0, 6, 7, 8, 9}, {0, 5, 7, 8, 9}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}, {0, 3, 7, 8, 9}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 8}, {0, 3, 5, 6, 7}, {0, 1, 7, 8, 9}, {0, 1, 6, 8, 9}, {0, 1, 6, 7, 9}, {0, 1, 6, 7, 8}, {0, 1, 5, 8, 9}, {0, 1, 5, 7, 9}, {0, 1, 5, 7, 8}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 8}, {0, 1, 5, 6, 7}, {0, 1, 3, 8, 9}, {0, 1, 3, 7, 9}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01003 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 8, 9} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 8, 9} ∨
        polygon = {3, 6, 7, 8, 9} ∨
        polygon = {3, 5, 7, 8, 9} ∨
        polygon = {3, 5, 6, 8, 9} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {1, 6, 7, 8, 9} ∨
        polygon = {1, 5, 7, 8, 9} ∨
        polygon = {1, 5, 6, 8, 9} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 5, 6, 7, 8} ∨
        polygon = {1, 3, 7, 8, 9} ∨
        polygon = {1, 3, 6, 8, 9} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 8, 9} ∨
        polygon = {0, 5, 7, 8, 9} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} ∨
        polygon = {0, 3, 7, 8, 9} ∨
        polygon = {0, 3, 6, 8, 9} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 8} ∨
        polygon = {0, 3, 5, 8, 9} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 7, 8} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 8} ∨
        polygon = {0, 3, 5, 6, 7} ∨
        polygon = {0, 1, 7, 8, 9} ∨
        polygon = {0, 1, 6, 8, 9} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 5, 8, 9} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 8, 9} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01003] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01515 :
    (({0, 1, 3, 5, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 8, 10}, {3, 6, 7, 8, 10}, {3, 5, 7, 8, 10}, {3, 5, 6, 8, 10}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 8}, {1, 6, 7, 8, 10}, {1, 5, 7, 8, 10}, {1, 5, 6, 8, 10}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 8}, {1, 3, 7, 8, 10}, {1, 3, 6, 8, 10}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 8}, {1, 3, 5, 8, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 8}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 8}, {1, 3, 5, 6, 7}, {0, 6, 7, 8, 10}, {0, 5, 7, 8, 10}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}, {0, 3, 7, 8, 10}, {0, 3, 6, 8, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 8}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 8}, {0, 3, 5, 6, 7}, {0, 1, 7, 8, 10}, {0, 1, 6, 8, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 8}, {0, 1, 5, 8, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 8}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 8}, {0, 1, 5, 6, 7}, {0, 1, 3, 8, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 8}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 8}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 8}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01515 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 8, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {3, 6, 7, 8, 10} ∨
        polygon = {3, 5, 7, 8, 10} ∨
        polygon = {3, 5, 6, 8, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 8} ∨
        polygon = {1, 6, 7, 8, 10} ∨
        polygon = {1, 5, 7, 8, 10} ∨
        polygon = {1, 5, 6, 8, 10} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 8} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 8} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 8} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} ∨
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
        polygon = {0, 1, 7, 8, 10} ∨
        polygon = {0, 1, 6, 8, 10} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 8} ∨
        polygon = {0, 1, 5, 8, 10} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 8} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 8} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 3, 8, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 8} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 8} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 8} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01515] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01771 :
    (({0, 1, 3, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {3, 6, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}, {1, 6, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 3, 7, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}, {0, 6, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 1, 7, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01771 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 10} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01771] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04843 :
    (({0, 1, 3, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {3, 6, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}, {1, 6, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 3, 7, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}, {0, 6, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 1, 7, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04843 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04843] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08939 :
    (({0, 1, 3, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {3, 6, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 9}, {1, 6, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 9}, {1, 3, 7, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}, {0, 6, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 1, 7, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08939 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 5, 7, 13} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 13} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08939] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17131 :
    (({0, 1, 3, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {3, 6, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 9}, {1, 6, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 9}, {1, 3, 7, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 9}, {1, 3, 5, 9, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}, {0, 6, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 9}, {0, 3, 7, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}, {0, 3, 5, 9, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}, {0, 1, 7, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}, {0, 1, 5, 9, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 3, 9, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17131 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 5, 7, 14} ∨
        polygon = {0, 3, 5, 7, 9} ∨
        polygon = {0, 3, 5, 6, 14} ∨
        polygon = {0, 3, 5, 6, 9} ∨
        polygon = {0, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17131] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05355 :
    (({0, 1, 3, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {3, 6, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {1, 6, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 3, 7, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 7}, {0, 6, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 3, 7, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}, {0, 1, 7, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 5, 7}, {0, 1, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05355 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 3, 5, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 5, 7, 12} ∨
        polygon = {0, 3, 5, 7, 10} ∨
        polygon = {0, 3, 5, 6, 12} ∨
        polygon = {0, 3, 5, 6, 10} ∨
        polygon = {0, 3, 5, 6, 7} ∨
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
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 5, 7} ∨
        polygon = {0, 1, 3, 5, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 3, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05355] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
