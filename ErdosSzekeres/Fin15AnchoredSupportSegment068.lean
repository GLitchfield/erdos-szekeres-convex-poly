module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 068. -/

theorem fin15Anchored_fiveFamily_mask04727 :
    (({0, 1, 2, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {2, 5, 6, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {1, 5, 6, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {1, 2, 6, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {0, 5, 6, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}, {0, 2, 6, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 1, 6, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04727 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04727] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08823 :
    (({0, 1, 2, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {2, 5, 6, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}, {1, 5, 6, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {1, 2, 6, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {0, 5, 6, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}, {0, 2, 6, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 1, 6, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 2, 9, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08823 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08823] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17015 :
    (({0, 1, 2, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {2, 5, 6, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 9}, {1, 5, 6, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 9}, {1, 2, 6, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {0, 5, 6, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 9}, {0, 2, 6, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 9}, {0, 2, 4, 9, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}, {0, 1, 6, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 9}, {0, 1, 4, 9, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 6}, {0, 1, 2, 9, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 9}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17015 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 9} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 9, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 9} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 9} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 9} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17015] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask03191 :
    (({0, 1, 2, 4, 5, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 11}, {2, 5, 6, 10, 11}, {2, 4, 6, 10, 11}, {2, 4, 5, 10, 11}, {2, 4, 5, 6, 11}, {2, 4, 5, 6, 10}, {1, 5, 6, 10, 11}, {1, 4, 6, 10, 11}, {1, 4, 5, 10, 11}, {1, 4, 5, 6, 11}, {1, 4, 5, 6, 10}, {1, 2, 6, 10, 11}, {1, 2, 5, 10, 11}, {1, 2, 5, 6, 11}, {1, 2, 5, 6, 10}, {1, 2, 4, 10, 11}, {1, 2, 4, 6, 11}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 11}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {0, 5, 6, 10, 11}, {0, 4, 6, 10, 11}, {0, 4, 5, 10, 11}, {0, 4, 5, 6, 11}, {0, 4, 5, 6, 10}, {0, 2, 6, 10, 11}, {0, 2, 5, 10, 11}, {0, 2, 5, 6, 11}, {0, 2, 5, 6, 10}, {0, 2, 4, 10, 11}, {0, 2, 4, 6, 11}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 11}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 1, 6, 10, 11}, {0, 1, 5, 10, 11}, {0, 1, 5, 6, 11}, {0, 1, 5, 6, 10}, {0, 1, 4, 10, 11}, {0, 1, 4, 6, 11}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 11}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 2, 10, 11}, {0, 1, 2, 6, 11}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 11}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 11}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask03191 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 11} ∨
        polygon = {2, 5, 6, 10, 11} ∨
        polygon = {2, 4, 6, 10, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 6, 11} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {1, 5, 6, 10, 11} ∨
        polygon = {1, 4, 6, 10, 11} ∨
        polygon = {1, 4, 5, 10, 11} ∨
        polygon = {1, 4, 5, 6, 11} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 2, 6, 10, 11} ∨
        polygon = {1, 2, 5, 10, 11} ∨
        polygon = {1, 2, 5, 6, 11} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 10, 11} ∨
        polygon = {1, 2, 4, 6, 11} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 11} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 10, 11} ∨
        polygon = {0, 4, 6, 10, 11} ∨
        polygon = {0, 4, 5, 10, 11} ∨
        polygon = {0, 4, 5, 6, 11} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 2, 6, 10, 11} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 5, 6, 11} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 10, 11} ∨
        polygon = {0, 2, 4, 6, 11} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 11} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 10, 11} ∨
        polygon = {0, 1, 5, 10, 11} ∨
        polygon = {0, 1, 5, 6, 11} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 6, 11} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 11} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 10, 11} ∨
        polygon = {0, 1, 2, 6, 11} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 11} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 11} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask03191] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05239 :
    (({0, 1, 2, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {2, 5, 6, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {1, 5, 6, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 2, 6, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {0, 5, 6, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}, {0, 2, 6, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 1, 6, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 6, 12}, {0, 1, 5, 6, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05239 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05239] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09335 :
    (({0, 1, 2, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {2, 5, 6, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {1, 5, 6, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 2, 6, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {0, 5, 6, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}, {0, 2, 6, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 1, 6, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 2, 10, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09335 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09335] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17527 :
    (({0, 1, 2, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {2, 5, 6, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}, {1, 5, 6, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}, {1, 2, 6, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {0, 5, 6, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}, {0, 2, 6, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}, {0, 1, 6, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 6}, {0, 1, 2, 10, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17527 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 10} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 10} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17527] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12407 :
    (({0, 1, 2, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {2, 5, 6, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {1, 5, 6, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 2, 6, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 6}, {0, 5, 6, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}, {0, 2, 6, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 6}, {0, 1, 6, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 6, 13}, {0, 1, 5, 6, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 6}, {0, 1, 2, 12, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12407 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 12, 13} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12407] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20599 :
    (({0, 1, 2, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {2, 5, 6, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {1, 5, 6, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 2, 6, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 6}, {0, 5, 6, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}, {0, 2, 6, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 6}, {0, 1, 6, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 6}, {0, 1, 2, 12, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20599 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 12, 14} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 12} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20599] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24695 :
    (({0, 1, 2, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {2, 5, 6, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {1, 5, 6, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 2, 6, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 6}, {0, 5, 6, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}, {0, 2, 6, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 6}, {0, 1, 6, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 6, 14}, {0, 1, 5, 6, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 6}, {0, 1, 2, 13, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 6}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 6}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24695 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 6, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 6, 14} ∨
        polygon = {1, 2, 5, 6, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 6} ∨
        polygon = {0, 5, 6, 13, 14} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 6, 14} ∨
        polygon = {0, 4, 5, 6, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 6, 14} ∨
        polygon = {0, 2, 5, 6, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 6} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 6, 14} ∨
        polygon = {0, 1, 5, 6, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 6} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 6} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24695] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01719 :
    (({0, 1, 2, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {2, 5, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {1, 5, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 2, 7, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {0, 5, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}, {0, 2, 7, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 1, 7, 9, 10}, {0, 1, 5, 9, 10}, {0, 1, 5, 7, 10}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01719 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01719] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04791 :
    (({0, 1, 2, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {2, 5, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {1, 5, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {1, 2, 7, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {0, 5, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}, {0, 2, 7, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 1, 7, 9, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04791 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04791] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08887 :
    (({0, 1, 2, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {2, 5, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}, {1, 5, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {1, 2, 7, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {0, 5, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}, {0, 2, 7, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 1, 7, 9, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08887 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08887] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17079 :
    (({0, 1, 2, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {2, 5, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 9}, {1, 5, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 9}, {1, 2, 7, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {0, 5, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}, {0, 2, 7, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 9}, {0, 2, 4, 9, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}, {0, 1, 7, 9, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 9}, {0, 1, 4, 9, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 4, 5, 7}, {0, 1, 2, 9, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 9}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 9}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17079 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 9} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 9} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 9} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 9} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17079] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask03255 :
    (({0, 1, 2, 4, 5, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 11}, {2, 5, 7, 10, 11}, {2, 4, 7, 10, 11}, {2, 4, 5, 10, 11}, {2, 4, 5, 7, 11}, {2, 4, 5, 7, 10}, {1, 5, 7, 10, 11}, {1, 4, 7, 10, 11}, {1, 4, 5, 10, 11}, {1, 4, 5, 7, 11}, {1, 4, 5, 7, 10}, {1, 2, 7, 10, 11}, {1, 2, 5, 10, 11}, {1, 2, 5, 7, 11}, {1, 2, 5, 7, 10}, {1, 2, 4, 10, 11}, {1, 2, 4, 7, 11}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 11}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {0, 5, 7, 10, 11}, {0, 4, 7, 10, 11}, {0, 4, 5, 10, 11}, {0, 4, 5, 7, 11}, {0, 4, 5, 7, 10}, {0, 2, 7, 10, 11}, {0, 2, 5, 10, 11}, {0, 2, 5, 7, 11}, {0, 2, 5, 7, 10}, {0, 2, 4, 10, 11}, {0, 2, 4, 7, 11}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 11}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 1, 7, 10, 11}, {0, 1, 5, 10, 11}, {0, 1, 5, 7, 11}, {0, 1, 5, 7, 10}, {0, 1, 4, 10, 11}, {0, 1, 4, 7, 11}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 11}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 2, 10, 11}, {0, 1, 2, 7, 11}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 11}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 11}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask03255 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 10, 11} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 11} ∨
        polygon = {2, 5, 7, 10, 11} ∨
        polygon = {2, 4, 7, 10, 11} ∨
        polygon = {2, 4, 5, 10, 11} ∨
        polygon = {2, 4, 5, 7, 11} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {1, 5, 7, 10, 11} ∨
        polygon = {1, 4, 7, 10, 11} ∨
        polygon = {1, 4, 5, 10, 11} ∨
        polygon = {1, 4, 5, 7, 11} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 2, 7, 10, 11} ∨
        polygon = {1, 2, 5, 10, 11} ∨
        polygon = {1, 2, 5, 7, 11} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 10, 11} ∨
        polygon = {1, 2, 4, 7, 11} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 11} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 10, 11} ∨
        polygon = {0, 4, 7, 10, 11} ∨
        polygon = {0, 4, 5, 10, 11} ∨
        polygon = {0, 4, 5, 7, 11} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 2, 7, 10, 11} ∨
        polygon = {0, 2, 5, 10, 11} ∨
        polygon = {0, 2, 5, 7, 11} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 10, 11} ∨
        polygon = {0, 2, 4, 7, 11} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 11} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 10, 11} ∨
        polygon = {0, 1, 5, 10, 11} ∨
        polygon = {0, 1, 5, 7, 11} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 10, 11} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 11} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 10, 11} ∨
        polygon = {0, 1, 2, 7, 11} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 11} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 11} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask03255] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05303 :
    (({0, 1, 2, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {2, 5, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {1, 5, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 2, 7, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {0, 5, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}, {0, 2, 7, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 1, 7, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 7, 12}, {0, 1, 5, 7, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05303 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05303] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09399 :
    (({0, 1, 2, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {2, 5, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {1, 5, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 2, 7, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {0, 5, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}, {0, 2, 7, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 1, 7, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09399 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09399] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17591 :
    (({0, 1, 2, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {2, 5, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}, {1, 5, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 2, 7, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {0, 5, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}, {0, 2, 7, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}, {0, 1, 7, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 7}, {0, 1, 2, 10, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17591 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 10} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 10} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17591] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12471 :
    (({0, 1, 2, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {2, 5, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {1, 5, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 2, 7, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {0, 5, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}, {0, 2, 7, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}, {0, 1, 7, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 7, 13}, {0, 1, 5, 7, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12471 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 12, 13} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12471] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20663 :
    (({0, 1, 2, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {2, 5, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {1, 5, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 2, 7, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {0, 5, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}, {0, 2, 7, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}, {0, 1, 7, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 7}, {0, 1, 2, 12, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20663 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 12, 14} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20663] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24759 :
    (({0, 1, 2, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {2, 5, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {1, 5, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 2, 7, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 7}, {0, 5, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}, {0, 2, 7, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 7}, {0, 1, 7, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 7, 14}, {0, 1, 5, 7, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 7}, {0, 1, 2, 13, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24759 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 7, 14} ∨
        polygon = {1, 2, 5, 7, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 7} ∨
        polygon = {0, 5, 7, 13, 14} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 7, 14} ∨
        polygon = {0, 4, 5, 7, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 7, 14} ∨
        polygon = {0, 2, 5, 7, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 7} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 7, 14} ∨
        polygon = {0, 1, 5, 7, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 7} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24759] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05687 :
    (({0, 1, 2, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {2, 5, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {1, 5, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {0, 5, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 1, 9, 10, 12}, {0, 1, 5, 10, 12}, {0, 1, 5, 9, 12}, {0, 1, 5, 9, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05687 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {0, 5, 9, 10, 12} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05687] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09783 :
    (({0, 1, 2, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {2, 5, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {1, 5, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {0, 5, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 1, 9, 10, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09783 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {0, 5, 9, 10, 13} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09783] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17975 :
    (({0, 1, 2, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {2, 5, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}, {1, 5, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}, {1, 2, 9, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {0, 5, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}, {0, 2, 9, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}, {0, 1, 9, 10, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 4, 5, 9}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17975 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 10} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {0, 5, 9, 10, 14} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 10} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17975] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12855 :
    (({0, 1, 2, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {2, 5, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {1, 5, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 2, 9, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {0, 5, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}, {0, 2, 9, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 1, 9, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 9, 13}, {0, 1, 5, 9, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12855 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {0, 5, 9, 12, 13} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12855] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21047 :
    (({0, 1, 2, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {2, 5, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {1, 5, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 2, 9, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {0, 5, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}, {0, 2, 9, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}, {0, 1, 9, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 9}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21047 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {0, 5, 9, 12, 14} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 12} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21047] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25143 :
    (({0, 1, 2, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {2, 5, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {1, 5, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 2, 9, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {0, 5, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}, {0, 2, 9, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}, {0, 1, 9, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 9, 14}, {0, 1, 5, 9, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25143 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {0, 5, 9, 13, 14} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25143] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13367 :
    (({0, 1, 2, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {2, 5, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {1, 5, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {0, 5, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 1, 10, 12, 13}, {0, 1, 5, 12, 13}, {0, 1, 5, 10, 13}, {0, 1, 5, 10, 12}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13367 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {0, 5, 10, 12, 13} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13367] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21559 :
    (({0, 1, 2, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {2, 5, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {1, 5, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 2, 10, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {0, 5, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}, {0, 2, 10, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 1, 10, 12, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 12}, {0, 1, 4, 12, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 12}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 2, 12, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 12}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21559 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 2, 10, 12, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {0, 5, 10, 12, 14} ∨
        polygon = {0, 4, 10, 12, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 2, 10, 12, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 1, 10, 12, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21559] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25655 :
    (({0, 1, 2, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {2, 5, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {1, 5, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 2, 10, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {0, 5, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}, {0, 2, 10, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 1, 10, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 10, 14}, {0, 1, 5, 10, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 10, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 2, 13, 14}, {0, 1, 2, 10, 14}, {0, 1, 2, 10, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25655 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 2, 10, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {0, 5, 10, 13, 14} ∨
        polygon = {0, 4, 10, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 2, 10, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 1, 10, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25655] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28727 :
    (({0, 1, 2, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {2, 5, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {1, 5, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 2, 12, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {0, 5, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}, {0, 2, 12, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 1, 12, 13, 14}, {0, 1, 5, 13, 14}, {0, 1, 5, 12, 14}, {0, 1, 5, 12, 13}, {0, 1, 4, 13, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 12, 13}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 2, 13, 14}, {0, 1, 2, 12, 14}, {0, 1, 2, 12, 13}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28727 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 5, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 2, 12, 13, 14} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {0, 5, 12, 13, 14} ∨
        polygon = {0, 4, 12, 13, 14} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 2, 12, 13, 14} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 1, 12, 13, 14} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28727] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01751 :
    (({0, 1, 2, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {2, 6, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {1, 6, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 2, 7, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {0, 6, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}, {0, 2, 7, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 1, 7, 9, 10}, {0, 1, 6, 9, 10}, {0, 1, 6, 7, 10}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01751 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 10} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01751] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask02775 :
    (({0, 1, 2, 4, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 11}, {2, 6, 7, 9, 11}, {2, 4, 7, 9, 11}, {2, 4, 6, 9, 11}, {2, 4, 6, 7, 11}, {2, 4, 6, 7, 9}, {1, 6, 7, 9, 11}, {1, 4, 7, 9, 11}, {1, 4, 6, 9, 11}, {1, 4, 6, 7, 11}, {1, 4, 6, 7, 9}, {1, 2, 7, 9, 11}, {1, 2, 6, 9, 11}, {1, 2, 6, 7, 11}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 11}, {1, 2, 4, 7, 11}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 11}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {0, 6, 7, 9, 11}, {0, 4, 7, 9, 11}, {0, 4, 6, 9, 11}, {0, 4, 6, 7, 11}, {0, 4, 6, 7, 9}, {0, 2, 7, 9, 11}, {0, 2, 6, 9, 11}, {0, 2, 6, 7, 11}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 11}, {0, 2, 4, 7, 11}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 11}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 1, 7, 9, 11}, {0, 1, 6, 9, 11}, {0, 1, 6, 7, 11}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 11}, {0, 1, 4, 7, 11}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 11}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 2, 9, 11}, {0, 1, 2, 7, 11}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 11}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 11}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask02775 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 9, 11} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 11} ∨
        polygon = {2, 6, 7, 9, 11} ∨
        polygon = {2, 4, 7, 9, 11} ∨
        polygon = {2, 4, 6, 9, 11} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 11} ∨
        polygon = {1, 4, 7, 9, 11} ∨
        polygon = {1, 4, 6, 9, 11} ∨
        polygon = {1, 4, 6, 7, 11} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 11} ∨
        polygon = {1, 2, 6, 9, 11} ∨
        polygon = {1, 2, 6, 7, 11} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 9, 11} ∨
        polygon = {1, 2, 4, 7, 11} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 11} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 11} ∨
        polygon = {0, 4, 7, 9, 11} ∨
        polygon = {0, 4, 6, 9, 11} ∨
        polygon = {0, 4, 6, 7, 11} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 11} ∨
        polygon = {0, 2, 6, 9, 11} ∨
        polygon = {0, 2, 6, 7, 11} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 11} ∨
        polygon = {0, 2, 4, 7, 11} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 11} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 9, 11} ∨
        polygon = {0, 1, 6, 9, 11} ∨
        polygon = {0, 1, 6, 7, 11} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 11} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 11} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 9, 11} ∨
        polygon = {0, 1, 2, 7, 11} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 11} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 11} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask02775] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04823 :
    (({0, 1, 2, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {2, 6, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}, {1, 6, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 2, 7, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {0, 6, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}, {0, 2, 7, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 1, 7, 9, 12}, {0, 1, 6, 9, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04823 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 12} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04823] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08919 :
    (({0, 1, 2, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {2, 6, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 9}, {1, 6, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 2, 7, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {0, 6, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}, {0, 2, 7, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 1, 7, 9, 13}, {0, 1, 6, 9, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08919 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 13} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08919] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17111 :
    (({0, 1, 2, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {2, 6, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 9}, {1, 6, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 9}, {1, 2, 7, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {0, 6, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 9}, {0, 2, 7, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 9}, {0, 2, 4, 9, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 1, 7, 9, 14}, {0, 1, 6, 9, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 9}, {0, 1, 4, 9, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 2, 9, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17111 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 9, 14} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17111] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05335 :
    (({0, 1, 2, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {2, 6, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {1, 6, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 2, 7, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {0, 6, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}, {0, 2, 7, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 1, 7, 10, 12}, {0, 1, 6, 10, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 10}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05335 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 10, 12} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05335] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09431 :
    (({0, 1, 2, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {2, 6, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {1, 6, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 2, 7, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {0, 6, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}, {0, 2, 7, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 1, 7, 10, 13}, {0, 1, 6, 10, 13}, {0, 1, 6, 7, 13}, {0, 1, 6, 7, 10}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09431 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 10, 13} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09431] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17623 :
    (({0, 1, 2, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {2, 6, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}, {1, 6, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 2, 7, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {0, 6, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}, {0, 2, 7, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 10}, {0, 2, 4, 10, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 1, 7, 10, 14}, {0, 1, 6, 10, 14}, {0, 1, 6, 7, 14}, {0, 1, 6, 7, 10}, {0, 1, 4, 10, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 2, 10, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17623 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 10, 14} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17623] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask06359 :
    (({0, 1, 2, 4, 6, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 11, 12}, {2, 6, 7, 11, 12}, {2, 4, 7, 11, 12}, {2, 4, 6, 11, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 11}, {1, 6, 7, 11, 12}, {1, 4, 7, 11, 12}, {1, 4, 6, 11, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 11}, {1, 2, 7, 11, 12}, {1, 2, 6, 11, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 11}, {1, 2, 4, 11, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 11}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 11}, {1, 2, 4, 6, 7}, {0, 6, 7, 11, 12}, {0, 4, 7, 11, 12}, {0, 4, 6, 11, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 11}, {0, 2, 7, 11, 12}, {0, 2, 6, 11, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 11}, {0, 2, 4, 11, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 11}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 11}, {0, 2, 4, 6, 7}, {0, 1, 7, 11, 12}, {0, 1, 6, 11, 12}, {0, 1, 6, 7, 12}, {0, 1, 6, 7, 11}, {0, 1, 4, 11, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 11}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 11}, {0, 1, 4, 6, 7}, {0, 1, 2, 11, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 11}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 11}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 11}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask06359 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 4, 6, 7, 11, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 11, 12} ∨
        polygon = {2, 6, 7, 11, 12} ∨
        polygon = {2, 4, 7, 11, 12} ∨
        polygon = {2, 4, 6, 11, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 11} ∨
        polygon = {1, 6, 7, 11, 12} ∨
        polygon = {1, 4, 7, 11, 12} ∨
        polygon = {1, 4, 6, 11, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 11} ∨
        polygon = {1, 2, 7, 11, 12} ∨
        polygon = {1, 2, 6, 11, 12} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 6, 7, 11} ∨
        polygon = {1, 2, 4, 11, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 11} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 11} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {0, 6, 7, 11, 12} ∨
        polygon = {0, 4, 7, 11, 12} ∨
        polygon = {0, 4, 6, 11, 12} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 4, 6, 7, 11} ∨
        polygon = {0, 2, 7, 11, 12} ∨
        polygon = {0, 2, 6, 11, 12} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 6, 7, 11} ∨
        polygon = {0, 2, 4, 11, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 11} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 11} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 1, 7, 11, 12} ∨
        polygon = {0, 1, 6, 11, 12} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 6, 7, 11} ∨
        polygon = {0, 1, 4, 11, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 11} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 11} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 2, 11, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 11} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 11} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 11} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 4, 6, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask06359] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
