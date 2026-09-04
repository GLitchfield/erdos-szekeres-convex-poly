module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 067. -/

theorem fin15Anchored_fiveFamily_mask04815 :
    (({0, 1, 2, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 12}, {2, 6, 7, 9, 12}, {2, 3, 7, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}, {1, 6, 7, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 2, 7, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {0, 6, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}, {0, 2, 7, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 1, 7, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04815 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04815] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08911 :
    (({0, 1, 2, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 13}, {2, 6, 7, 9, 13}, {2, 3, 7, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 9}, {1, 6, 7, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {1, 2, 7, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {0, 6, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}, {0, 2, 7, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 9}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 1, 7, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08911 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08911] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17103 :
    (({0, 1, 2, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 14}, {2, 6, 7, 9, 14}, {2, 3, 7, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 9}, {1, 6, 7, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 9}, {1, 2, 7, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 9}, {1, 2, 3, 9, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {0, 6, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}, {0, 2, 7, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 9}, {0, 2, 3, 9, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 1, 7, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}, {0, 1, 3, 9, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 2, 9, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17103 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17103] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05327 :
    (({0, 1, 2, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 12}, {2, 6, 7, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {1, 6, 7, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 2, 7, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {0, 6, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}, {0, 2, 7, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 1, 7, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05327 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05327] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09423 :
    (({0, 1, 2, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 13}, {2, 6, 7, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {1, 6, 7, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 2, 7, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {0, 6, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}, {0, 2, 7, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 1, 7, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09423 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09423] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17615 :
    (({0, 1, 2, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 14}, {2, 6, 7, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}, {1, 6, 7, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 2, 7, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {0, 6, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}, {0, 2, 7, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 1, 7, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 2, 10, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17615 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17615] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12495 :
    (({0, 1, 2, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 13}, {2, 6, 7, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 12}, {1, 6, 7, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}, {1, 2, 7, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 7}, {0, 6, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}, {0, 2, 7, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 1, 7, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12495 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 12, 13} ∨
        polygon = {2, 6, 7, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12495] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20687 :
    (({0, 1, 2, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 14}, {2, 6, 7, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 12}, {1, 6, 7, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}, {1, 2, 7, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 7}, {0, 6, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}, {0, 2, 7, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 1, 7, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 2, 12, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20687 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 12, 14} ∨
        polygon = {2, 6, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {1, 6, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20687] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24783 :
    (({0, 1, 2, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 13, 14}, {2, 6, 7, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 13}, {1, 6, 7, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}, {1, 2, 7, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 7}, {0, 6, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}, {0, 2, 7, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 7}, {0, 1, 7, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 7}, {0, 1, 2, 13, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24783 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 7, 13, 14} ∨
        polygon = {2, 6, 7, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {1, 6, 7, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {0, 6, 7, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24783] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05711 :
    (({0, 1, 2, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 12}, {2, 6, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 9, 10}, {1, 6, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 9, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {0, 6, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 1, 9, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 9, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05711 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 6, 9, 10, 12} ∨
        polygon = {2, 6, 9, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 12} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {0, 6, 9, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05711] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09807 :
    (({0, 1, 2, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 13}, {2, 6, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 10}, {1, 6, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {0, 6, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 1, 9, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09807 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 6, 9, 10, 13} ∨
        polygon = {2, 6, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {0, 6, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09807] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17999 :
    (({0, 1, 2, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 14}, {2, 6, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 10}, {1, 6, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}, {1, 2, 9, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {0, 6, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}, {0, 2, 9, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 1, 9, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17999 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 9, 10, 14} ∨
        polygon = {2, 6, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {1, 6, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {0, 6, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17999] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12879 :
    (({0, 1, 2, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 13}, {2, 6, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 9, 12}, {1, 6, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}, {1, 2, 9, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 9, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {0, 6, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}, {0, 2, 9, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 1, 9, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 9, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12879 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 6, 9, 12, 13} ∨
        polygon = {2, 6, 9, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {0, 6, 9, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12879] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21071 :
    (({0, 1, 2, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 14}, {2, 6, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 12}, {1, 6, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}, {1, 2, 9, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {0, 6, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}, {0, 2, 9, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 1, 9, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21071 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 9, 12, 14} ∨
        polygon = {2, 6, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {1, 6, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {0, 6, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21071] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25167 :
    (({0, 1, 2, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 13, 14}, {2, 6, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 9, 13}, {1, 6, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}, {1, 2, 9, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 9, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {0, 6, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}, {0, 2, 9, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 1, 9, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 9, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25167 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 9, 13, 14} ∨
        polygon = {2, 6, 9, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {1, 6, 9, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {0, 6, 9, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25167] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13391 :
    (({0, 1, 2, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 13}, {2, 6, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 10, 12}, {1, 6, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 6, 12, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 10, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {0, 6, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 1, 10, 12, 13}, {0, 1, 6, 12, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 10, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13391 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 6, 10, 12, 13} ∨
        polygon = {2, 6, 10, 12, 13} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 13} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {0, 6, 10, 12, 13} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13391] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21583 :
    (({0, 1, 2, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 14}, {2, 6, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 12}, {1, 6, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {0, 6, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 1, 10, 12, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21583 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 10, 12, 14} ∨
        polygon = {2, 6, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {1, 6, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {0, 6, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21583] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25679 :
    (({0, 1, 2, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 13, 14}, {2, 6, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 10, 13}, {1, 6, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 10, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {0, 6, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 1, 10, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 10, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25679 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 10, 13, 14} ∨
        polygon = {2, 6, 10, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {1, 6, 10, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {0, 6, 10, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25679] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28751 :
    (({0, 1, 2, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 12, 13, 14}, {2, 6, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 6, 12, 14}, {2, 3, 6, 12, 13}, {1, 6, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 6, 13, 14}, {1, 2, 6, 12, 14}, {1, 2, 6, 12, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {0, 6, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 1, 12, 13, 14}, {0, 1, 6, 13, 14}, {0, 1, 6, 12, 14}, {0, 1, 6, 12, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28751 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 6, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 6, 12, 13, 14} ∨
        polygon = {2, 6, 12, 13, 14} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {1, 6, 12, 13, 14} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {0, 6, 12, 13, 14} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28751] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05775 :
    (({0, 1, 2, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 12}, {2, 7, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 7, 9, 12}, {2, 3, 7, 9, 10}, {1, 7, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 7, 10, 12}, {1, 2, 7, 9, 12}, {1, 2, 7, 9, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {0, 7, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 1, 9, 10, 12}, {0, 1, 7, 10, 12}, {0, 1, 7, 9, 12}, {0, 1, 7, 9, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05775 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 7, 9, 10, 12} ∨
        polygon = {2, 7, 9, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 12} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {0, 7, 9, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05775] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09871 :
    (({0, 1, 2, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 13}, {2, 7, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 10}, {1, 7, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {0, 7, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 1, 9, 10, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09871 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 7, 9, 10, 13} ∨
        polygon = {2, 7, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {0, 7, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09871] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask18063 :
    (({0, 1, 2, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 14}, {2, 7, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 10}, {1, 7, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}, {1, 2, 9, 10, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {0, 7, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}, {0, 2, 9, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 1, 9, 10, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask18063 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 7, 9, 10, 14} ∨
        polygon = {2, 7, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {1, 7, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {0, 7, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask18063] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12943 :
    (({0, 1, 2, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 13}, {2, 7, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 9, 13}, {2, 3, 7, 9, 12}, {1, 7, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}, {1, 2, 9, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 9, 13}, {1, 2, 7, 9, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {0, 7, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}, {0, 2, 9, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 1, 9, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 9, 13}, {0, 1, 7, 9, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12943 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 7, 9, 12, 13} ∨
        polygon = {2, 7, 9, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {0, 7, 9, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12943] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21135 :
    (({0, 1, 2, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 14}, {2, 7, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 12}, {1, 7, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}, {1, 2, 9, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {0, 7, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}, {0, 2, 9, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 1, 9, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21135 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 7, 9, 12, 14} ∨
        polygon = {2, 7, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {1, 7, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {0, 7, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21135] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25231 :
    (({0, 1, 2, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 13, 14}, {2, 7, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 9, 14}, {2, 3, 7, 9, 13}, {1, 7, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}, {1, 2, 9, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 9, 14}, {1, 2, 7, 9, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {0, 7, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}, {0, 2, 9, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 1, 9, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 9, 14}, {0, 1, 7, 9, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25231 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 7, 9, 13, 14} ∨
        polygon = {2, 7, 9, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {1, 7, 9, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {0, 7, 9, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25231] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13455 :
    (({0, 1, 2, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 13}, {2, 7, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 7, 10, 13}, {2, 3, 7, 10, 12}, {1, 7, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 7, 12, 13}, {1, 2, 7, 10, 13}, {1, 2, 7, 10, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {0, 7, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 1, 10, 12, 13}, {0, 1, 7, 12, 13}, {0, 1, 7, 10, 13}, {0, 1, 7, 10, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13455 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 7, 10, 12, 13} ∨
        polygon = {2, 7, 10, 12, 13} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 13} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {0, 7, 10, 12, 13} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13455] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21647 :
    (({0, 1, 2, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 14}, {2, 7, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 12}, {1, 7, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {0, 7, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 1, 10, 12, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21647 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 7, 10, 12, 14} ∨
        polygon = {2, 7, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {1, 7, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {0, 7, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21647] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25743 :
    (({0, 1, 2, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 13, 14}, {2, 7, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 10, 14}, {2, 3, 7, 10, 13}, {1, 7, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 10, 14}, {1, 2, 7, 10, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {0, 7, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 1, 10, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 10, 14}, {0, 1, 7, 10, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25743 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 7, 10, 13, 14} ∨
        polygon = {2, 7, 10, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {1, 7, 10, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {0, 7, 10, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25743] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28815 :
    (({0, 1, 2, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 12, 13, 14}, {2, 7, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 7, 12, 14}, {2, 3, 7, 12, 13}, {1, 7, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 7, 13, 14}, {1, 2, 7, 12, 14}, {1, 2, 7, 12, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {0, 7, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 1, 12, 13, 14}, {0, 1, 7, 13, 14}, {0, 1, 7, 12, 14}, {0, 1, 7, 12, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28815 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 7, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 7, 12, 13, 14} ∨
        polygon = {2, 7, 12, 13, 14} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {1, 7, 12, 13, 14} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {0, 7, 12, 13, 14} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28815] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13839 :
    (({0, 1, 2, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 13}, {2, 9, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 9, 10, 13}, {2, 3, 9, 10, 12}, {1, 9, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 9, 12, 13}, {1, 2, 9, 10, 13}, {1, 2, 9, 10, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {0, 9, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 1, 10, 12, 13}, {0, 1, 9, 12, 13}, {0, 1, 9, 10, 13}, {0, 1, 9, 10, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13839 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 9, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 9, 10, 12, 13} ∨
        polygon = {2, 9, 10, 12, 13} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 13} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {0, 9, 10, 12, 13} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13839] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask22031 :
    (({0, 1, 2, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 14}, {2, 9, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 12}, {1, 9, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {0, 9, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 1, 10, 12, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask22031 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 9, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 9, 10, 12, 14} ∨
        polygon = {2, 9, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {1, 9, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {0, 9, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask22031] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask26127 :
    (({0, 1, 2, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 13, 14}, {2, 9, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 10, 14}, {2, 3, 9, 10, 13}, {1, 9, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 10, 14}, {1, 2, 9, 10, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {0, 9, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 1, 10, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 10, 14}, {0, 1, 9, 10, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask26127 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 9, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 9, 10, 13, 14} ∨
        polygon = {2, 9, 10, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {1, 9, 10, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {0, 9, 10, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask26127] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29199 :
    (({0, 1, 2, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 12, 13, 14}, {2, 9, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 9, 12, 14}, {2, 3, 9, 12, 13}, {1, 9, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 9, 13, 14}, {1, 2, 9, 12, 14}, {1, 2, 9, 12, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {0, 9, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 1, 12, 13, 14}, {0, 1, 9, 13, 14}, {0, 1, 9, 12, 14}, {0, 1, 9, 12, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29199 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 9, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 9, 12, 13, 14} ∨
        polygon = {2, 9, 12, 13, 14} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {1, 9, 12, 13, 14} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {0, 9, 12, 13, 14} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29199] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask29711 :
    (({0, 1, 2, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 10, 12, 13, 14}, {2, 10, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 10, 12, 14}, {2, 3, 10, 12, 13}, {1, 10, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 10, 13, 14}, {1, 2, 10, 12, 14}, {1, 2, 10, 12, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {0, 10, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 1, 12, 13, 14}, {0, 1, 10, 13, 14}, {0, 1, 10, 12, 14}, {0, 1, 10, 12, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 12, 14}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 14}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask29711 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 10, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 10, 12, 13, 14} ∨
        polygon = {2, 10, 12, 13, 14} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {1, 10, 12, 13, 14} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {0, 10, 12, 13, 14} ∨
        polygon = {0, 3, 12, 13, 14} ∨
        polygon = {0, 3, 10, 13, 14} ∨
        polygon = {0, 3, 10, 12, 14} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask29711] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00759 :
    (({0, 1, 2, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {2, 5, 6, 7, 9}, {2, 4, 6, 7, 9}, {2, 4, 5, 7, 9}, {2, 4, 5, 6, 9}, {2, 4, 5, 6, 7}, {1, 5, 6, 7, 9}, {1, 4, 6, 7, 9}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}, {1, 2, 6, 7, 9}, {1, 2, 5, 7, 9}, {1, 2, 5, 6, 9}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {0, 5, 6, 7, 9}, {0, 4, 6, 7, 9}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}, {0, 2, 6, 7, 9}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 1, 6, 7, 9}, {0, 1, 5, 7, 9}, {0, 1, 5, 6, 9}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00759 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 9} ∨
        polygon = {2, 5, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 9} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 9} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00759] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01271 :
    (({0, 1, 2, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {2, 5, 6, 7, 10}, {2, 4, 6, 7, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 7}, {1, 5, 6, 7, 10}, {1, 4, 6, 7, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}, {1, 2, 6, 7, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {0, 5, 6, 7, 10}, {0, 4, 6, 7, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}, {0, 2, 6, 7, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 1, 6, 7, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01271 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 10} ∨
        polygon = {2, 5, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01271] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04343 :
    (({0, 1, 2, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {2, 5, 6, 7, 12}, {2, 4, 6, 7, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 7}, {1, 5, 6, 7, 12}, {1, 4, 6, 7, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}, {1, 2, 6, 7, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {0, 5, 6, 7, 12}, {0, 4, 6, 7, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}, {0, 2, 6, 7, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 1, 6, 7, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04343 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 12} ∨
        polygon = {2, 5, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 7} ∨
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
        polygon = {0, 5, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04343] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08439 :
    (({0, 1, 2, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {2, 5, 6, 7, 13}, {2, 4, 6, 7, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 7}, {1, 5, 6, 7, 13}, {1, 4, 6, 7, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 7}, {1, 2, 6, 7, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {0, 5, 6, 7, 13}, {0, 4, 6, 7, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 7}, {0, 2, 6, 7, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 1, 6, 7, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 2, 7, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08439 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 7, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08439] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16631 :
    (({0, 1, 2, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {2, 5, 6, 7, 14}, {2, 4, 6, 7, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 7}, {1, 5, 6, 7, 14}, {1, 4, 6, 7, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 7}, {1, 2, 6, 7, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {0, 5, 6, 7, 14}, {0, 4, 6, 7, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 7}, {0, 2, 6, 7, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 7}, {0, 2, 4, 7, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}, {0, 1, 6, 7, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 7}, {0, 1, 4, 7, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 7}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 7}, {0, 1, 4, 5, 6}, {0, 1, 2, 7, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 7}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 7}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16631 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 7, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 7} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 7} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 7} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 7} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16631] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01655 :
    (({0, 1, 2, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {2, 5, 6, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {1, 5, 6, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 2, 6, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {0, 5, 6, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}, {0, 2, 6, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 1, 6, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 6, 10}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01655 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01655] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
