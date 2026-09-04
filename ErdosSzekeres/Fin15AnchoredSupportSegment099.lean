module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 099. -/

theorem fin15Anchored_fiveFamily_mask25274 :
    (({1, 3, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 13}, {3, 7, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {1, 7, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25274 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 7, 9, 13, 14} →
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
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25274] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13498 :
    (({1, 3, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 10, 12}, {3, 7, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {1, 7, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13498 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 7, 10, 12, 13} →
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
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13498] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21690 :
    (({1, 3, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 12}, {3, 7, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {1, 7, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21690 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 7, 10, 12, 14} →
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
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21690] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25786 :
    (({1, 3, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 13}, {3, 7, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {1, 7, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25786 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 7, 10, 13, 14} →
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
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25786] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28858 :
    (({1, 3, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 12, 13}, {3, 7, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {1, 7, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28858 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 7, 12, 13, 14} →
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
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28858] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10042 :
    (({1, 3, 4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 13}, {4, 8, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 10}, {3, 8, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 10}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 10}, {3, 4, 5, 8, 9}, {1, 8, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 8, 10, 13}, {1, 5, 8, 9, 13}, {1, 5, 8, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 8, 9, 13}, {1, 4, 8, 9, 10}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 10}, {1, 4, 5, 8, 9}, {1, 3, 9, 10, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 10}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 10}, {1, 3, 5, 8, 9}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 10}, {1, 3, 4, 8, 9}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10042 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 8, 9, 10, 13} →
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
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 10} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10042] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25402 :
    (({1, 3, 4, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 13, 14}, {4, 8, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 9, 14}, {4, 5, 8, 9, 13}, {3, 8, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 8, 13, 14}, {3, 5, 8, 9, 14}, {3, 5, 8, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 8, 9, 14}, {3, 4, 8, 9, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 8, 14}, {3, 4, 5, 8, 13}, {3, 4, 5, 8, 9}, {1, 8, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 8, 13, 14}, {1, 5, 8, 9, 14}, {1, 5, 8, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 8, 9, 14}, {1, 4, 8, 9, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 9}, {1, 3, 9, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 8, 9, 14}, {1, 3, 8, 9, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 9}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 9}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25402 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 8, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {4, 8, 9, 13, 14} ∨
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {4, 5, 8, 13, 14} ∨
        polygon = {4, 5, 8, 9, 14} ∨
        polygon = {4, 5, 8, 9, 13} ∨
        polygon = {3, 8, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 5, 8, 13, 14} ∨
        polygon = {3, 5, 8, 9, 14} ∨
        polygon = {3, 5, 8, 9, 13} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 8, 13, 14} ∨
        polygon = {3, 4, 8, 9, 14} ∨
        polygon = {3, 4, 8, 9, 13} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 8, 14} ∨
        polygon = {3, 4, 5, 8, 13} ∨
        polygon = {3, 4, 5, 8, 9} ∨
        polygon = {1, 8, 9, 13, 14} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 5, 8, 13, 14} ∨
        polygon = {1, 5, 8, 9, 14} ∨
        polygon = {1, 5, 8, 9, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 8, 13, 14} ∨
        polygon = {1, 4, 8, 9, 14} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 8, 14} ∨
        polygon = {1, 4, 5, 8, 13} ∨
        polygon = {1, 4, 5, 8, 9} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 8, 13, 14} ∨
        polygon = {1, 3, 8, 9, 14} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 8, 14} ∨
        polygon = {1, 3, 5, 8, 13} ∨
        polygon = {1, 3, 5, 8, 9} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 9} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25402] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13882 :
    (({1, 3, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {1, 9, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13882 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 9, 10, 12, 13} →
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
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13882] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22074 :
    (({1, 3, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {1, 9, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22074 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 9, 10, 12, 14} →
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
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22074] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26170 :
    (({1, 3, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {1, 9, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26170 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 9, 10, 13, 14} →
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
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26170] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29242 :
    (({1, 3, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {1, 9, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29242 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 9, 12, 13, 14} →
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
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29242] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29754 :
    (({1, 3, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {1, 10, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 10, 12, 14}, {1, 5, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29754 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 5, 10, 12, 13, 14} →
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
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29754] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05594 :
    (({1, 3, 4, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {4, 7, 8, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 8, 12}, {4, 6, 7, 8, 10}, {3, 7, 8, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}, {3, 4, 8, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 8, 12}, {3, 4, 7, 8, 10}, {3, 4, 6, 10, 12}, {3, 4, 6, 8, 12}, {3, 4, 6, 8, 10}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 8}, {1, 7, 8, 10, 12}, {1, 6, 8, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 8, 12}, {1, 6, 7, 8, 10}, {1, 4, 8, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 8, 12}, {1, 4, 7, 8, 10}, {1, 4, 6, 10, 12}, {1, 4, 6, 8, 12}, {1, 4, 6, 8, 10}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 8}, {1, 3, 8, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 10}, {1, 3, 6, 10, 12}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 10}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 8}, {1, 3, 4, 10, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 10}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 8}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 8}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05594 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 8, 10, 12} →
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
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 8, 12} ∨
        polygon = {1, 3, 7, 8, 10} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 8, 12} ∨
        polygon = {1, 3, 6, 8, 10} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05594] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05850 :
    (({1, 3, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05850 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 9, 10, 12} →
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
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05850] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09946 :
    (({1, 3, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09946 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 9, 10, 13} →
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
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09946] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18138 :
    (({1, 3, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}, {3, 7, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 4, 10, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18138 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 9, 10, 14} →
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
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18138] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13018 :
    (({1, 3, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}, {3, 7, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13018 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 9, 12, 13} →
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
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13018] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21210 :
    (({1, 3, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}, {3, 7, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 4, 9, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 4, 12, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21210 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 9, 12, 14} →
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
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21210] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25306 :
    (({1, 3, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}, {3, 7, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {1, 7, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 13}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25306 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 9, 13, 14} →
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
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25306] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13530 :
    (({1, 3, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}, {3, 7, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {1, 7, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13530 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 10, 12, 13} →
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
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13530] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21722 :
    (({1, 3, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 12}, {3, 7, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {1, 7, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21722 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 10, 12, 14} →
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
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21722] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25818 :
    (({1, 3, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}, {3, 7, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {1, 7, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25818 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 10, 13, 14} →
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
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25818] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28890 :
    (({1, 3, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}, {3, 7, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}, {1, 7, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28890 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 7, 12, 13, 14} →
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
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28890] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13914 :
    (({1, 3, 4, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 9, 10, 13}, {4, 6, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {1, 9, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 9, 10, 13}, {1, 6, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13914 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13914] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22106 :
    (({1, 3, 4, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}, {1, 9, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22106 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22106] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26202 :
    (({1, 3, 4, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}, {1, 9, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26202 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 10, 14} ∨
        polygon = {4, 6, 9, 10, 13} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26202] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29274 :
    (({1, 3, 4, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}, {1, 9, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29274 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 9, 13, 14} ∨
        polygon = {4, 6, 9, 12, 14} ∨
        polygon = {4, 6, 9, 12, 13} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29274] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29786 :
    (({1, 3, 4, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 10, 12, 14}, {4, 6, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}, {1, 10, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 10, 12, 14}, {1, 6, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29786 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 6, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 6, 12, 13, 14} ∨
        polygon = {4, 6, 10, 13, 14} ∨
        polygon = {4, 6, 10, 12, 14} ∨
        polygon = {4, 6, 10, 12, 13} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 12} ∨
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
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29786] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13978 :
    (({1, 3, 4, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 7, 9, 12, 13}, {4, 7, 9, 10, 13}, {4, 7, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {1, 9, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 7, 9, 12, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13978 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 7, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 7, 9, 10, 12} ∨
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
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
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
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13978] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22170 :
    (({1, 3, 4, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 12}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}, {1, 9, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 12}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22170 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 7, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 12} ∨
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
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 10} ∨
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
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22170] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26266 :
    (({1, 3, 4, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 13}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}, {1, 9, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 13}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26266 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 7, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 10, 14} ∨
        polygon = {4, 7, 9, 10, 13} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 7, 9, 10, 13} ∨
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
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 10} ∨
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
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26266] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29338 :
    (({1, 3, 4, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 12, 13}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}, {1, 9, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29338 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 7, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 9, 13, 14} ∨
        polygon = {4, 7, 9, 12, 14} ∨
        polygon = {4, 7, 9, 12, 13} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 7, 9, 12, 13} ∨
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
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 12} ∨
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
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29338] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29850 :
    (({1, 3, 4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 10, 12, 14}, {4, 7, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}, {1, 10, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29850 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 7, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 7, 12, 13, 14} ∨
        polygon = {4, 7, 10, 13, 14} ∨
        polygon = {4, 7, 10, 12, 14} ∨
        polygon = {4, 7, 10, 12, 13} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {3, 7, 10, 12, 13} ∨
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
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 12} ∨
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
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29850] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14106 :
    (({1, 3, 4, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 8, 9, 12, 13}, {4, 8, 9, 10, 13}, {4, 8, 9, 10, 12}, {3, 9, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 8, 9, 12, 13}, {3, 8, 9, 10, 13}, {3, 8, 9, 10, 12}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {3, 4, 8, 12, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 10, 12}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 12}, {3, 4, 8, 9, 10}, {1, 9, 10, 12, 13}, {1, 8, 10, 12, 13}, {1, 8, 9, 12, 13}, {1, 8, 9, 10, 13}, {1, 8, 9, 10, 12}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 4, 8, 12, 13}, {1, 4, 8, 10, 13}, {1, 4, 8, 10, 12}, {1, 4, 8, 9, 13}, {1, 4, 8, 9, 12}, {1, 4, 8, 9, 10}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 8, 12, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 10, 12}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 12}, {1, 3, 8, 9, 10}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 10}, {1, 3, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14106 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {4, 8, 10, 12, 13} ∨
        polygon = {4, 8, 9, 12, 13} ∨
        polygon = {4, 8, 9, 10, 13} ∨
        polygon = {4, 8, 9, 10, 12} ∨
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {3, 8, 10, 12, 13} ∨
        polygon = {3, 8, 9, 12, 13} ∨
        polygon = {3, 8, 9, 10, 13} ∨
        polygon = {3, 8, 9, 10, 12} ∨
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
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 8, 10, 12, 13} ∨
        polygon = {1, 8, 9, 12, 13} ∨
        polygon = {1, 8, 9, 10, 13} ∨
        polygon = {1, 8, 9, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 8, 12, 13} ∨
        polygon = {1, 4, 8, 10, 13} ∨
        polygon = {1, 4, 8, 10, 12} ∨
        polygon = {1, 4, 8, 9, 13} ∨
        polygon = {1, 4, 8, 9, 12} ∨
        polygon = {1, 4, 8, 9, 10} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 8, 12, 13} ∨
        polygon = {1, 3, 8, 10, 13} ∨
        polygon = {1, 3, 8, 10, 12} ∨
        polygon = {1, 3, 8, 9, 13} ∨
        polygon = {1, 3, 8, 9, 12} ∨
        polygon = {1, 3, 8, 9, 10} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 8, 13} ∨
        polygon = {1, 3, 4, 8, 12} ∨
        polygon = {1, 3, 4, 8, 10} ∨
        polygon = {1, 3, 4, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14106] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30234 :
    (({1, 3, 4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 9, 10, 13, 14}, {4, 9, 10, 12, 14}, {4, 9, 10, 12, 13}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}, {1, 10, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 9, 10, 13, 14}, {1, 9, 10, 12, 14}, {1, 9, 10, 12, 13}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30234 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 4, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {4, 10, 12, 13, 14} ∨
        polygon = {4, 9, 12, 13, 14} ∨
        polygon = {4, 9, 10, 13, 14} ∨
        polygon = {4, 9, 10, 12, 14} ∨
        polygon = {4, 9, 10, 12, 13} ∨
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {3, 9, 10, 12, 13} ∨
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
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 12} ∨
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
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30234] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05866 :
    (({1, 3, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 6, 9, 10, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}, {3, 5, 9, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}, {1, 5, 9, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05866 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 5, 6, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05866] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09962 :
    (({1, 3, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 6, 9, 10, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}, {3, 5, 9, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}, {1, 5, 9, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 10}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09962 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 5, 6, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09962] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18154 :
    (({1, 3, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 6, 9, 10, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 10}, {3, 7, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}, {3, 5, 9, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}, {1, 5, 9, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 10}, {1, 5, 6, 10, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18154 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 5, 6, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {5, 7, 9, 10, 14} ∨
        polygon = {5, 6, 9, 10, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18154] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13034 :
    (({1, 3, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {3, 7, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}, {3, 5, 9, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}, {1, 5, 9, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13034 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 5, 6, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 7, 12, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13034] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21226 :
    (({1, 3, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {3, 7, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}, {3, 5, 9, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}, {1, 5, 9, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 12}, {1, 5, 6, 12, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21226 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 3, 5, 6, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 6, 9, 12, 14} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 9, 14} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 3, 5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21226] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
