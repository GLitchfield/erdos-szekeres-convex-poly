module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 092. -/

theorem fin15Anchored_fiveFamily_mask06113 :
    (({0, 5, 6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {6, 8, 9, 10, 12}, {6, 7, 9, 10, 12}, {6, 7, 8, 10, 12}, {6, 7, 8, 9, 12}, {6, 7, 8, 9, 10}, {5, 8, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}, {5, 6, 9, 10, 12}, {5, 6, 8, 10, 12}, {5, 6, 8, 9, 12}, {5, 6, 8, 9, 10}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 10}, {5, 6, 7, 8, 9}, {0, 8, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 6, 9, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 5, 9, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06113 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 7, 9, 10, 12} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 9, 12} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
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
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06113] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask10209 :
    (({0, 5, 6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {6, 8, 9, 10, 13}, {6, 7, 9, 10, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 10}, {5, 8, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 10}, {5, 6, 9, 10, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 10}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 10}, {5, 6, 7, 8, 9}, {0, 8, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 6, 9, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 5, 9, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask10209 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 10} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 7, 9, 10, 13} ∨
        polygon = {5, 7, 8, 10, 13} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 10} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 8, 9, 10} ∨
        polygon = {5, 6, 7, 10, 13} ∨
        polygon = {5, 6, 7, 9, 13} ∨
        polygon = {5, 6, 7, 9, 10} ∨
        polygon = {5, 6, 7, 8, 13} ∨
        polygon = {5, 6, 7, 8, 10} ∨
        polygon = {5, 6, 7, 8, 9} ∨
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
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask10209] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18401 :
    (({0, 5, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {6, 8, 9, 10, 14}, {6, 7, 9, 10, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 10}, {5, 8, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 10}, {5, 6, 9, 10, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 10}, {5, 6, 7, 10, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 10}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 10}, {5, 6, 7, 8, 9}, {0, 8, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 10}, {0, 6, 9, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 10}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}, {0, 5, 9, 10, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 10}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18401 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 9, 10, 14} →
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
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18401] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13281 :
    (({0, 5, 6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 13}, {6, 8, 9, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 12}, {5, 8, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 8, 12, 13}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 12}, {5, 6, 9, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 12}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 9}, {0, 8, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 6, 9, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 5, 9, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13281 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 9, 12, 13} →
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
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13281] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21473 :
    (({0, 5, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 14}, {6, 8, 9, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 12}, {5, 8, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 12}, {5, 6, 9, 12, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 12}, {5, 6, 7, 12, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 9}, {0, 8, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 12}, {0, 6, 9, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 9}, {0, 5, 9, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21473 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 9, 12, 14} →
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
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21473] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25569 :
    (({0, 5, 6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {6, 8, 9, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 13}, {5, 8, 9, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 13}, {5, 6, 9, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 9}, {0, 8, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 8, 13, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}, {0, 6, 9, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 9}, {0, 5, 9, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 9}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 9}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25569 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 9, 13, 14} →
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
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 9} ∨
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
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 9} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25569] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13793 :
    (({0, 5, 6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 10, 12}, {5, 8, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 8, 12, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 10, 12}, {5, 6, 10, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 10}, {0, 8, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 6, 10, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 5, 10, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13793 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 10, 12, 13} →
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
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13793] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21985 :
    (({0, 5, 6, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 12}, {5, 8, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 12}, {5, 6, 10, 12, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 12}, {5, 6, 7, 12, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 10}, {0, 8, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 12}, {0, 6, 10, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 5, 10, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21985 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {5, 8, 10, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 10, 14} ∨
        polygon = {5, 7, 8, 10, 12} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 8, 12, 14} ∨
        polygon = {5, 6, 8, 10, 14} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 8, 14} ∨
        polygon = {5, 6, 7, 8, 12} ∨
        polygon = {5, 6, 7, 8, 10} ∨
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
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21985] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26081 :
    (({0, 5, 6, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 13}, {5, 8, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 13}, {5, 6, 10, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 10}, {0, 8, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 8, 13, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 6, 10, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 5, 10, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26081 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 8, 10, 13, 14} →
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
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 10} ∨
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
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 8} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26081] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14049 :
    (({0, 5, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {5, 9, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {0, 9, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14049 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 9, 10, 12, 13} →
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
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14049] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22241 :
    (({0, 5, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}, {5, 9, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 12}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {5, 6, 7, 12, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}, {0, 9, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22241 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 9, 10, 12, 14} →
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
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22241] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26337 :
    (({0, 5, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {5, 9, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}, {0, 9, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26337 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 9, 10, 13, 14} →
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
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26337] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29409 :
    (({0, 5, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}, {5, 9, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}, {0, 9, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29409 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 9, 12, 13, 14} →
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
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29409] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask23777 :
    (({0, 5, 6, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 12, 14}, {6, 10, 11, 12, 14}, {6, 7, 11, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 11, 14}, {6, 7, 10, 11, 12}, {5, 10, 11, 12, 14}, {5, 7, 11, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 11, 14}, {5, 7, 10, 11, 12}, {5, 6, 11, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 11, 14}, {5, 6, 10, 11, 12}, {5, 6, 7, 12, 14}, {5, 6, 7, 11, 14}, {5, 6, 7, 11, 12}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}, {5, 6, 7, 10, 11}, {0, 10, 11, 12, 14}, {0, 7, 11, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 11, 14}, {0, 7, 10, 11, 12}, {0, 6, 11, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 11, 14}, {0, 6, 10, 11, 12}, {0, 6, 7, 12, 14}, {0, 6, 7, 11, 14}, {0, 6, 7, 11, 12}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 10, 11}, {0, 5, 11, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 11, 14}, {0, 5, 10, 11, 12}, {0, 5, 7, 12, 14}, {0, 5, 7, 11, 14}, {0, 5, 7, 11, 12}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 10, 11}, {0, 5, 6, 12, 14}, {0, 5, 6, 11, 14}, {0, 5, 6, 11, 12}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 10, 11}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 11}, {0, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask23777 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 10, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {7, 10, 11, 12, 14} ∨
        polygon = {6, 10, 11, 12, 14} ∨
        polygon = {6, 7, 11, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 11, 14} ∨
        polygon = {6, 7, 10, 11, 12} ∨
        polygon = {5, 10, 11, 12, 14} ∨
        polygon = {5, 7, 11, 12, 14} ∨
        polygon = {5, 7, 10, 12, 14} ∨
        polygon = {5, 7, 10, 11, 14} ∨
        polygon = {5, 7, 10, 11, 12} ∨
        polygon = {5, 6, 11, 12, 14} ∨
        polygon = {5, 6, 10, 12, 14} ∨
        polygon = {5, 6, 10, 11, 14} ∨
        polygon = {5, 6, 10, 11, 12} ∨
        polygon = {5, 6, 7, 12, 14} ∨
        polygon = {5, 6, 7, 11, 14} ∨
        polygon = {5, 6, 7, 11, 12} ∨
        polygon = {5, 6, 7, 10, 14} ∨
        polygon = {5, 6, 7, 10, 12} ∨
        polygon = {5, 6, 7, 10, 11} ∨
        polygon = {0, 10, 11, 12, 14} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 11, 14} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 6, 11, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 11, 14} ∨
        polygon = {0, 6, 10, 11, 12} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 11, 14} ∨
        polygon = {0, 6, 7, 11, 12} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 11} ∨
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
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 11, 14} ∨
        polygon = {0, 5, 6, 11, 12} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 10, 11} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 11} ∨
        polygon = {0, 5, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask23777] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29921 :
    (({0, 5, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}, {0, 10, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29921 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 7, 10, 12, 13, 14} →
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
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 5, 6, 7, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29921] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14177 :
    (({0, 5, 6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 8, 9, 12, 13}, {6, 8, 9, 10, 13}, {6, 8, 9, 10, 12}, {5, 9, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 8, 9, 12, 13}, {5, 8, 9, 10, 13}, {5, 8, 9, 10, 12}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 12}, {5, 6, 8, 9, 10}, {0, 9, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14177 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 8, 10, 12, 13} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 8, 9, 10, 13} ∨
        polygon = {5, 8, 9, 10, 12} ∨
        polygon = {5, 6, 10, 12, 13} ∨
        polygon = {5, 6, 9, 12, 13} ∨
        polygon = {5, 6, 9, 10, 13} ∨
        polygon = {5, 6, 9, 10, 12} ∨
        polygon = {5, 6, 8, 12, 13} ∨
        polygon = {5, 6, 8, 10, 13} ∨
        polygon = {5, 6, 8, 10, 12} ∨
        polygon = {5, 6, 8, 9, 13} ∨
        polygon = {5, 6, 8, 9, 12} ∨
        polygon = {5, 6, 8, 9, 10} ∨
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
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14177] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22369 :
    (({0, 5, 6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 12}, {5, 9, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 12}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}, {5, 6, 8, 12, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 12}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 12}, {5, 6, 8, 9, 10}, {0, 9, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 12}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 6, 8, 12, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 8, 12, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22369 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 8, 9, 10, 12, 14} →
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
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22369] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26465 :
    (({0, 5, 6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 13}, {5, 9, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 9, 13, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 13}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {5, 6, 8, 13, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 10}, {0, 9, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 8, 13, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}, {0, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26465 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 8, 9, 10, 13, 14} →
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
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 10} ∨
        polygon = {0, 5, 6, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26465] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30049 :
    (({0, 5, 6, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 10, 12, 14}, {6, 8, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 10, 12, 14}, {5, 8, 10, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {5, 6, 8, 13, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}, {0, 10, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 8, 13, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 8, 13, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 12}, {0, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30049 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 8, 10, 12, 13, 14} →
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
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 8, 12, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 8, 14} ∨
        polygon = {0, 5, 6, 8, 13} ∨
        polygon = {0, 5, 6, 8, 12} ∨
        polygon = {0, 5, 6, 8, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30049] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30305 :
    (({0, 5, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30305 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 6, 9, 10, 12, 13, 14} →
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
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 5, 6, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30305] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14241 :
    (({0, 5, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {7, 9, 10, 12, 13}, {7, 8, 10, 12, 13}, {7, 8, 9, 12, 13}, {7, 8, 9, 10, 13}, {7, 8, 9, 10, 12}, {5, 9, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 8, 9, 12, 13}, {5, 8, 9, 10, 13}, {5, 8, 9, 10, 12}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {5, 7, 8, 12, 13}, {5, 7, 8, 10, 13}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}, {0, 9, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14241 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 7, 8, 9, 10, 12, 13} →
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
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14241] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22433 :
    (({0, 5, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {7, 9, 10, 12, 14}, {7, 8, 10, 12, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 12}, {5, 9, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 12}, {5, 7, 10, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 12}, {5, 7, 8, 12, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}, {0, 9, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 12}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 7, 8, 12, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}, {0, 5, 8, 12, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22433 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 7, 8, 9, 10, 12, 14} →
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
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22433] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26529 :
    (({0, 5, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {7, 9, 10, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 13}, {5, 9, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 9, 13, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 13}, {5, 7, 10, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {5, 7, 8, 13, 14}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 13}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 10}, {0, 9, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 8, 13, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 10}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26529 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 7, 8, 9, 10, 13, 14} →
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
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 10} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 10} ∨
        polygon = {0, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26529] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29601 :
    (({0, 5, 7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 12, 13}, {5, 9, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 8, 9, 13, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 12, 13}, {5, 7, 12, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}, {5, 7, 8, 13, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 12, 13}, {5, 7, 8, 9, 14}, {5, 7, 8, 9, 13}, {5, 7, 8, 9, 12}, {0, 9, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 7, 8, 13, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 12, 13}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 8, 13, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 12, 13}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29601 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 7, 8, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 8, 12, 13, 14} ∨
        polygon = {5, 8, 9, 13, 14} ∨
        polygon = {5, 8, 9, 12, 14} ∨
        polygon = {5, 8, 9, 12, 13} ∨
        polygon = {5, 7, 12, 13, 14} ∨
        polygon = {5, 7, 9, 13, 14} ∨
        polygon = {5, 7, 9, 12, 14} ∨
        polygon = {5, 7, 9, 12, 13} ∨
        polygon = {5, 7, 8, 13, 14} ∨
        polygon = {5, 7, 8, 12, 14} ∨
        polygon = {5, 7, 8, 12, 13} ∨
        polygon = {5, 7, 8, 9, 14} ∨
        polygon = {5, 7, 8, 9, 13} ∨
        polygon = {5, 7, 8, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 8, 12, 13, 14} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29601] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30113 :
    (({0, 5, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 10, 12, 14}, {7, 8, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 10, 12, 14}, {5, 8, 10, 12, 13}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {5, 7, 8, 13, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 12, 13}, {5, 7, 8, 10, 14}, {5, 7, 8, 10, 13}, {5, 7, 8, 10, 12}, {0, 10, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 8, 13, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 8, 13, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30113 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 7, 8, 10, 12, 13, 14} →
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
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 8, 14} ∨
        polygon = {0, 5, 7, 8, 13} ∨
        polygon = {0, 5, 7, 8, 12} ∨
        polygon = {0, 5, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30113] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30369 :
    (({0, 5, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30369 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 7, 9, 10, 12, 13, 14} →
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
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 5, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30369] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30497 :
    (({0, 5, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {8, 10, 12, 13, 14}, {8, 9, 12, 13, 14}, {8, 9, 10, 13, 14}, {8, 9, 10, 12, 14}, {8, 9, 10, 12, 13}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {5, 8, 12, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 10, 12, 14}, {5, 8, 10, 12, 13}, {5, 8, 9, 13, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 12, 13}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 13}, {5, 8, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}, {0, 8, 9, 13, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 8, 13, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 12, 13}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30497 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 8, 9, 10, 12, 13, 14} →
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
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 8, 12, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 8, 9, 10, 12} ∨
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
        polygon = {0, 5, 8, 13, 14} ∨
        polygon = {0, 5, 8, 12, 14} ∨
        polygon = {0, 5, 8, 12, 13} ∨
        polygon = {0, 5, 8, 10, 14} ∨
        polygon = {0, 5, 8, 10, 13} ∨
        polygon = {0, 5, 8, 10, 12} ∨
        polygon = {0, 5, 8, 9, 14} ∨
        polygon = {0, 5, 8, 9, 13} ∨
        polygon = {0, 5, 8, 9, 12} ∨
        polygon = {0, 5, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30497] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask32289 :
    (({0, 5, 9, 10, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{10, 11, 12, 13, 14}, {9, 11, 12, 13, 14}, {9, 10, 12, 13, 14}, {9, 10, 11, 13, 14}, {9, 10, 11, 12, 14}, {9, 10, 11, 12, 13}, {5, 11, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 10, 11, 13, 14}, {5, 10, 11, 12, 14}, {5, 10, 11, 12, 13}, {5, 9, 12, 13, 14}, {5, 9, 11, 13, 14}, {5, 9, 11, 12, 14}, {5, 9, 11, 12, 13}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}, {5, 9, 10, 11, 14}, {5, 9, 10, 11, 13}, {5, 9, 10, 11, 12}, {0, 11, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 10, 11, 13, 14}, {0, 10, 11, 12, 14}, {0, 10, 11, 12, 13}, {0, 9, 12, 13, 14}, {0, 9, 11, 13, 14}, {0, 9, 11, 12, 14}, {0, 9, 11, 12, 13}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 9, 10, 11, 14}, {0, 9, 10, 11, 13}, {0, 9, 10, 11, 12}, {0, 5, 12, 13, 14}, {0, 5, 11, 13, 14}, {0, 5, 11, 12, 14}, {0, 5, 11, 12, 13}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}, {0, 5, 10, 11, 14}, {0, 5, 10, 11, 13}, {0, 5, 10, 11, 12}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}, {0, 5, 9, 11, 14}, {0, 5, 9, 11, 13}, {0, 5, 9, 11, 12}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}, {0, 5, 9, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask32289 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 5, 9, 10, 11, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {10, 11, 12, 13, 14} ∨
        polygon = {9, 11, 12, 13, 14} ∨
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {9, 10, 11, 13, 14} ∨
        polygon = {9, 10, 11, 12, 14} ∨
        polygon = {9, 10, 11, 12, 13} ∨
        polygon = {5, 11, 12, 13, 14} ∨
        polygon = {5, 10, 12, 13, 14} ∨
        polygon = {5, 10, 11, 13, 14} ∨
        polygon = {5, 10, 11, 12, 14} ∨
        polygon = {5, 10, 11, 12, 13} ∨
        polygon = {5, 9, 12, 13, 14} ∨
        polygon = {5, 9, 11, 13, 14} ∨
        polygon = {5, 9, 11, 12, 14} ∨
        polygon = {5, 9, 11, 12, 13} ∨
        polygon = {5, 9, 10, 13, 14} ∨
        polygon = {5, 9, 10, 12, 14} ∨
        polygon = {5, 9, 10, 12, 13} ∨
        polygon = {5, 9, 10, 11, 14} ∨
        polygon = {5, 9, 10, 11, 13} ∨
        polygon = {5, 9, 10, 11, 12} ∨
        polygon = {0, 11, 12, 13, 14} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 10, 11, 13, 14} ∨
        polygon = {0, 10, 11, 12, 14} ∨
        polygon = {0, 10, 11, 12, 13} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 11, 13, 14} ∨
        polygon = {0, 9, 11, 12, 14} ∨
        polygon = {0, 9, 11, 12, 13} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 9, 10, 11, 14} ∨
        polygon = {0, 9, 10, 11, 13} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 5, 11, 13, 14} ∨
        polygon = {0, 5, 11, 12, 14} ∨
        polygon = {0, 5, 11, 12, 13} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 5, 10, 11, 14} ∨
        polygon = {0, 5, 10, 11, 13} ∨
        polygon = {0, 5, 10, 11, 12} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 5, 9, 11, 14} ∨
        polygon = {0, 5, 9, 11, 13} ∨
        polygon = {0, 5, 9, 11, 12} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 5, 9, 10, 11} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 5, 9, 10, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask32289] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask14273 :
    (({0, 6, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {7, 9, 10, 12, 13}, {7, 8, 10, 12, 13}, {7, 8, 9, 12, 13}, {7, 8, 9, 10, 13}, {7, 8, 9, 10, 12}, {6, 9, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 8, 9, 12, 13}, {6, 8, 9, 10, 13}, {6, 8, 9, 10, 12}, {6, 7, 10, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {6, 7, 8, 12, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 10, 12}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 12}, {6, 7, 8, 9, 10}, {0, 9, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 7, 10, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask14273 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 7, 8, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 9, 13} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
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
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask14273] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22465 :
    (({0, 6, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {7, 9, 10, 12, 14}, {7, 8, 10, 12, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 12}, {6, 9, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 12}, {6, 7, 10, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}, {6, 7, 8, 12, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 12}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 12}, {6, 7, 8, 9, 10}, {0, 9, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 12}, {0, 7, 10, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 7, 8, 12, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 6, 8, 12, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22465 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 7, 8, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 10, 12} ∨
        polygon = {6, 7, 8, 9, 14} ∨
        polygon = {6, 7, 8, 9, 12} ∨
        polygon = {6, 7, 8, 9, 10} ∨
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
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22465] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26561 :
    (({0, 6, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {7, 9, 10, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 13}, {6, 9, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 13}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {6, 7, 8, 13, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 13}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 10}, {0, 9, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 9, 13, 14}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 7, 10, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 8, 13, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 8, 13, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26561 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 7, 8, 9, 10, 13, 14} →
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
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 10} ∨
        polygon = {0, 6, 7, 8, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26561] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30145 :
    (({0, 6, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 10, 12, 14}, {7, 8, 10, 12, 13}, {6, 10, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 10, 12, 14}, {6, 8, 10, 12, 13}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}, {6, 7, 8, 13, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 12, 13}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 13}, {6, 7, 8, 10, 12}, {0, 10, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 8, 13, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 8, 13, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30145 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 7, 8, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {8, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 8, 12, 13, 14} ∨
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 8, 13, 14} ∨
        polygon = {6, 7, 8, 12, 14} ∨
        polygon = {6, 7, 8, 12, 13} ∨
        polygon = {6, 7, 8, 10, 14} ∨
        polygon = {6, 7, 8, 10, 13} ∨
        polygon = {6, 7, 8, 10, 12} ∨
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
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 8, 14} ∨
        polygon = {0, 6, 7, 8, 13} ∨
        polygon = {0, 6, 7, 8, 12} ∨
        polygon = {0, 6, 7, 8, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30145] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16065 :
    (({0, 6, 7, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 12, 13}, {7, 10, 11, 12, 13}, {7, 9, 11, 12, 13}, {7, 9, 10, 12, 13}, {7, 9, 10, 11, 13}, {7, 9, 10, 11, 12}, {6, 10, 11, 12, 13}, {6, 9, 11, 12, 13}, {6, 9, 10, 12, 13}, {6, 9, 10, 11, 13}, {6, 9, 10, 11, 12}, {6, 7, 11, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 10, 11, 13}, {6, 7, 10, 11, 12}, {6, 7, 9, 12, 13}, {6, 7, 9, 11, 13}, {6, 7, 9, 11, 12}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {6, 7, 9, 10, 11}, {0, 10, 11, 12, 13}, {0, 9, 11, 12, 13}, {0, 9, 10, 12, 13}, {0, 9, 10, 11, 13}, {0, 9, 10, 11, 12}, {0, 7, 11, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 10, 11, 13}, {0, 7, 10, 11, 12}, {0, 7, 9, 12, 13}, {0, 7, 9, 11, 13}, {0, 7, 9, 11, 12}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 7, 9, 10, 11}, {0, 6, 11, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 10, 11, 13}, {0, 6, 10, 11, 12}, {0, 6, 9, 12, 13}, {0, 6, 9, 11, 13}, {0, 6, 9, 11, 12}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 9, 10, 11}, {0, 6, 7, 12, 13}, {0, 6, 7, 11, 13}, {0, 6, 7, 11, 12}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 10, 11}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 11}, {0, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16065 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 7, 9, 10, 11, 12, 13} →
      polygon.card = 5 →
        polygon = {9, 10, 11, 12, 13} ∨
        polygon = {7, 10, 11, 12, 13} ∨
        polygon = {7, 9, 11, 12, 13} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {7, 9, 10, 11, 13} ∨
        polygon = {7, 9, 10, 11, 12} ∨
        polygon = {6, 10, 11, 12, 13} ∨
        polygon = {6, 9, 11, 12, 13} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 9, 10, 11, 13} ∨
        polygon = {6, 9, 10, 11, 12} ∨
        polygon = {6, 7, 11, 12, 13} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 10, 11, 13} ∨
        polygon = {6, 7, 10, 11, 12} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 9, 11, 13} ∨
        polygon = {6, 7, 9, 11, 12} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 11} ∨
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
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 11, 13} ∨
        polygon = {0, 6, 7, 11, 12} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 11} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 11} ∨
        polygon = {0, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 7, 9, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16065] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24257 :
    (({0, 6, 7, 9, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 12, 14}, {7, 10, 11, 12, 14}, {7, 9, 11, 12, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 11, 14}, {7, 9, 10, 11, 12}, {6, 10, 11, 12, 14}, {6, 9, 11, 12, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 11, 14}, {6, 9, 10, 11, 12}, {6, 7, 11, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 11, 14}, {6, 7, 10, 11, 12}, {6, 7, 9, 12, 14}, {6, 7, 9, 11, 14}, {6, 7, 9, 11, 12}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}, {6, 7, 9, 10, 11}, {0, 10, 11, 12, 14}, {0, 9, 11, 12, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 11, 14}, {0, 9, 10, 11, 12}, {0, 7, 11, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 11, 14}, {0, 7, 10, 11, 12}, {0, 7, 9, 12, 14}, {0, 7, 9, 11, 14}, {0, 7, 9, 11, 12}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 12}, {0, 7, 9, 10, 11}, {0, 6, 11, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 11, 14}, {0, 6, 10, 11, 12}, {0, 6, 9, 12, 14}, {0, 6, 9, 11, 14}, {0, 6, 9, 11, 12}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}, {0, 6, 9, 10, 11}, {0, 6, 7, 12, 14}, {0, 6, 7, 11, 14}, {0, 6, 7, 11, 12}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}, {0, 6, 7, 10, 11}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 11}, {0, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24257 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 7, 9, 10, 11, 12, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 11, 12, 14} ∨
        polygon = {7, 10, 11, 12, 14} ∨
        polygon = {7, 9, 11, 12, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 11, 14} ∨
        polygon = {7, 9, 10, 11, 12} ∨
        polygon = {6, 10, 11, 12, 14} ∨
        polygon = {6, 9, 11, 12, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 11, 14} ∨
        polygon = {6, 9, 10, 11, 12} ∨
        polygon = {6, 7, 11, 12, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 11, 14} ∨
        polygon = {6, 7, 10, 11, 12} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 11, 14} ∨
        polygon = {6, 7, 9, 11, 12} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 12} ∨
        polygon = {6, 7, 9, 10, 11} ∨
        polygon = {0, 10, 11, 12, 14} ∨
        polygon = {0, 9, 11, 12, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 11, 14} ∨
        polygon = {0, 9, 10, 11, 12} ∨
        polygon = {0, 7, 11, 12, 14} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 7, 10, 11, 14} ∨
        polygon = {0, 7, 10, 11, 12} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 7, 9, 11, 14} ∨
        polygon = {0, 7, 9, 11, 12} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 7, 9, 10, 11} ∨
        polygon = {0, 6, 11, 12, 14} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 6, 10, 11, 14} ∨
        polygon = {0, 6, 10, 11, 12} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 6, 9, 11, 14} ∨
        polygon = {0, 6, 9, 11, 12} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 6, 9, 10, 11} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 11, 14} ∨
        polygon = {0, 6, 7, 11, 12} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 10, 11} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 11} ∨
        polygon = {0, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 7, 9, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24257] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30401 :
    (({0, 6, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30401 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 7, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 7, 12, 13, 14} ∨
        polygon = {6, 7, 10, 13, 14} ∨
        polygon = {6, 7, 10, 12, 14} ∨
        polygon = {6, 7, 10, 12, 13} ∨
        polygon = {6, 7, 9, 13, 14} ∨
        polygon = {6, 7, 9, 12, 14} ∨
        polygon = {6, 7, 9, 12, 13} ∨
        polygon = {6, 7, 9, 10, 14} ∨
        polygon = {6, 7, 9, 10, 13} ∨
        polygon = {6, 7, 9, 10, 12} ∨
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
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 6, 7, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30401] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30529 :
    (({0, 6, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {8, 10, 12, 13, 14}, {8, 9, 12, 13, 14}, {8, 9, 10, 13, 14}, {8, 9, 10, 12, 14}, {8, 9, 10, 12, 13}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}, {6, 8, 12, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 10, 12, 14}, {6, 8, 10, 12, 13}, {6, 8, 9, 13, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 12, 13}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 13}, {6, 8, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}, {0, 8, 9, 13, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}, {0, 6, 8, 13, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30529 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 6, 8, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {8, 10, 12, 13, 14} ∨
        polygon = {8, 9, 12, 13, 14} ∨
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {6, 10, 12, 13, 14} ∨
        polygon = {6, 9, 12, 13, 14} ∨
        polygon = {6, 9, 10, 13, 14} ∨
        polygon = {6, 9, 10, 12, 14} ∨
        polygon = {6, 9, 10, 12, 13} ∨
        polygon = {6, 8, 12, 13, 14} ∨
        polygon = {6, 8, 10, 13, 14} ∨
        polygon = {6, 8, 10, 12, 14} ∨
        polygon = {6, 8, 10, 12, 13} ∨
        polygon = {6, 8, 9, 13, 14} ∨
        polygon = {6, 8, 9, 12, 14} ∨
        polygon = {6, 8, 9, 12, 13} ∨
        polygon = {6, 8, 9, 10, 14} ∨
        polygon = {6, 8, 9, 10, 13} ∨
        polygon = {6, 8, 9, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 8, 12, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 8, 9, 10, 12} ∨
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
        polygon = {0, 6, 8, 13, 14} ∨
        polygon = {0, 6, 8, 12, 14} ∨
        polygon = {0, 6, 8, 12, 13} ∨
        polygon = {0, 6, 8, 10, 14} ∨
        polygon = {0, 6, 8, 10, 13} ∨
        polygon = {0, 6, 8, 10, 12} ∨
        polygon = {0, 6, 8, 9, 14} ∨
        polygon = {0, 6, 8, 9, 13} ∨
        polygon = {0, 6, 8, 9, 12} ∨
        polygon = {0, 6, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 6, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30529] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask30593 :
    (({0, 7, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {8, 10, 12, 13, 14}, {8, 9, 12, 13, 14}, {8, 9, 10, 13, 14}, {8, 9, 10, 12, 14}, {8, 9, 10, 12, 13}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}, {7, 8, 12, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 10, 12, 14}, {7, 8, 10, 12, 13}, {7, 8, 9, 13, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 12, 13}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 13}, {7, 8, 9, 10, 12}, {0, 10, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 9, 10, 13, 14}, {0, 9, 10, 12, 14}, {0, 9, 10, 12, 13}, {0, 8, 12, 13, 14}, {0, 8, 10, 13, 14}, {0, 8, 10, 12, 14}, {0, 8, 10, 12, 13}, {0, 8, 9, 13, 14}, {0, 8, 9, 12, 14}, {0, 8, 9, 12, 13}, {0, 8, 9, 10, 14}, {0, 8, 9, 10, 13}, {0, 8, 9, 10, 12}, {0, 7, 12, 13, 14}, {0, 7, 10, 13, 14}, {0, 7, 10, 12, 14}, {0, 7, 10, 12, 13}, {0, 7, 9, 13, 14}, {0, 7, 9, 12, 14}, {0, 7, 9, 12, 13}, {0, 7, 9, 10, 14}, {0, 7, 9, 10, 13}, {0, 7, 9, 10, 12}, {0, 7, 8, 13, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask30593 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 7, 8, 9, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {9, 10, 12, 13, 14} ∨
        polygon = {8, 10, 12, 13, 14} ∨
        polygon = {8, 9, 12, 13, 14} ∨
        polygon = {8, 9, 10, 13, 14} ∨
        polygon = {8, 9, 10, 12, 14} ∨
        polygon = {8, 9, 10, 12, 13} ∨
        polygon = {7, 10, 12, 13, 14} ∨
        polygon = {7, 9, 12, 13, 14} ∨
        polygon = {7, 9, 10, 13, 14} ∨
        polygon = {7, 9, 10, 12, 14} ∨
        polygon = {7, 9, 10, 12, 13} ∨
        polygon = {7, 8, 12, 13, 14} ∨
        polygon = {7, 8, 10, 13, 14} ∨
        polygon = {7, 8, 10, 12, 14} ∨
        polygon = {7, 8, 10, 12, 13} ∨
        polygon = {7, 8, 9, 13, 14} ∨
        polygon = {7, 8, 9, 12, 14} ∨
        polygon = {7, 8, 9, 12, 13} ∨
        polygon = {7, 8, 9, 10, 14} ∨
        polygon = {7, 8, 9, 10, 13} ∨
        polygon = {7, 8, 9, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 8, 12, 13, 14} ∨
        polygon = {0, 8, 10, 13, 14} ∨
        polygon = {0, 8, 10, 12, 14} ∨
        polygon = {0, 8, 10, 12, 13} ∨
        polygon = {0, 8, 9, 13, 14} ∨
        polygon = {0, 8, 9, 12, 14} ∨
        polygon = {0, 8, 9, 12, 13} ∨
        polygon = {0, 8, 9, 10, 14} ∨
        polygon = {0, 8, 9, 10, 13} ∨
        polygon = {0, 8, 9, 10, 12} ∨
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
        polygon = {0, 7, 8, 13, 14} ∨
        polygon = {0, 7, 8, 12, 14} ∨
        polygon = {0, 7, 8, 12, 13} ∨
        polygon = {0, 7, 8, 10, 14} ∨
        polygon = {0, 7, 8, 10, 13} ∨
        polygon = {0, 7, 8, 10, 12} ∨
        polygon = {0, 7, 8, 9, 14} ∨
        polygon = {0, 7, 8, 9, 13} ∨
        polygon = {0, 7, 8, 9, 12} ∨
        polygon = {0, 7, 8, 9, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 7, 8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask30593] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00766 :
    (({1, 2, 3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {3, 5, 6, 7, 9}, {3, 4, 6, 7, 9}, {3, 4, 5, 7, 9}, {3, 4, 5, 6, 9}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 9}, {2, 4, 6, 7, 9}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 9}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {1, 5, 6, 7, 9}, {1, 4, 6, 7, 9}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 9}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {1, 2, 6, 7, 9}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00766 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {3, 5, 6, 7, 9} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00766] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01278 :
    (({1, 2, 3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {3, 5, 6, 7, 10}, {3, 4, 6, 7, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 10}, {2, 4, 6, 7, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {1, 5, 6, 7, 10}, {1, 4, 6, 7, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {1, 2, 6, 7, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01278 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {3, 5, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01278] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04350 :
    (({1, 2, 3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {3, 5, 6, 7, 12}, {3, 4, 6, 7, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 12}, {2, 4, 6, 7, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {1, 5, 6, 7, 12}, {1, 4, 6, 7, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {1, 2, 6, 7, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {1, 2, 3, 7, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04350 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {3, 5, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 3, 4, 5, 6} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04350] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
