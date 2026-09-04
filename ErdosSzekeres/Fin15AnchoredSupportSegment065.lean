module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 065. -/

theorem fin15Anchored_fiveFamily_mask08767 :
    (({0, 1, 2, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 13}, {2, 4, 5, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {1, 4, 5, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 2, 5, 9, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 3, 9, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}, {0, 4, 5, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}, {0, 2, 5, 9, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}, {0, 2, 3, 9, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}, {0, 1, 5, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 9}, {0, 1, 3, 9, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}, {0, 1, 2, 9, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08767 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 9, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 2, 5, 9, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 9, 13} ∨
        polygon = {0, 3, 5, 9, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 5, 9, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 9, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08767] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16959 :
    (({0, 1, 2, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 14}, {2, 4, 5, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 9}, {1, 4, 5, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 9}, {1, 2, 5, 9, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 9}, {1, 2, 3, 9, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}, {0, 4, 5, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}, {0, 2, 5, 9, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 9}, {0, 2, 3, 9, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 5}, {0, 1, 5, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 9}, {0, 1, 3, 9, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 5}, {0, 1, 2, 9, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16959 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 9, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 2, 5, 9, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 9} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 9, 14} ∨
        polygon = {0, 3, 5, 9, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 9} ∨
        polygon = {0, 2, 5, 9, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 9} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 9, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 9} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16959] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05183 :
    (({0, 1, 2, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 12}, {2, 4, 5, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {1, 4, 5, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 2, 5, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 5}, {0, 4, 5, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}, {0, 2, 5, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}, {0, 1, 5, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 5, 12}, {0, 1, 4, 5, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 5, 12}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}, {0, 1, 2, 10, 12}, {0, 1, 2, 5, 12}, {0, 1, 2, 5, 10}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05183 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 2, 5, 10, 12} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 10, 12} ∨
        polygon = {0, 3, 5, 10, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 2, 5, 10, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 10, 12} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05183] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09279 :
    (({0, 1, 2, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 13}, {2, 4, 5, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {1, 4, 5, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 2, 5, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 5}, {0, 4, 5, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}, {0, 2, 5, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}, {0, 1, 5, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}, {0, 1, 2, 10, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09279 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 2, 5, 10, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 10, 13} ∨
        polygon = {0, 3, 5, 10, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 2, 5, 10, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 10, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09279] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17471 :
    (({0, 1, 2, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 14}, {2, 4, 5, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {1, 4, 5, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 2, 5, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 5}, {0, 4, 5, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}, {0, 2, 5, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 5}, {0, 1, 5, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 5}, {0, 1, 2, 10, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17471 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 2, 5, 10, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 10, 14} ∨
        polygon = {0, 3, 5, 10, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 10} ∨
        polygon = {0, 2, 5, 10, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 10, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17471] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12351 :
    (({0, 1, 2, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 13}, {2, 4, 5, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {1, 4, 5, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 2, 5, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 5}, {0, 4, 5, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}, {0, 2, 5, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 5}, {0, 1, 5, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 5, 13}, {0, 1, 4, 5, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 5, 13}, {0, 1, 3, 5, 12}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 5}, {0, 1, 2, 12, 13}, {0, 1, 2, 5, 13}, {0, 1, 2, 5, 12}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12351 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 2, 5, 12, 13} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 12, 13} ∨
        polygon = {0, 3, 5, 12, 13} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 2, 5, 12, 13} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 12, 13} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12351] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20543 :
    (({0, 1, 2, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 14}, {2, 4, 5, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {1, 4, 5, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 2, 5, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 5}, {0, 4, 5, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}, {0, 2, 5, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 5}, {0, 1, 5, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 5}, {0, 1, 2, 12, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20543 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 2, 5, 12, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 12, 14} ∨
        polygon = {0, 3, 5, 12, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 12} ∨
        polygon = {0, 2, 5, 12, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 12, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20543] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24639 :
    (({0, 1, 2, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 13, 14}, {2, 4, 5, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {1, 4, 5, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 2, 5, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 5}, {0, 4, 5, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}, {0, 2, 5, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 5}, {0, 1, 5, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 5, 14}, {0, 1, 4, 5, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 5, 14}, {0, 1, 3, 5, 13}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 5}, {0, 1, 2, 13, 14}, {0, 1, 2, 5, 14}, {0, 1, 2, 5, 13}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24639 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 5, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 2, 5, 13, 14} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 5, 14} ∨
        polygon = {1, 2, 4, 5, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 5} ∨
        polygon = {0, 4, 5, 13, 14} ∨
        polygon = {0, 3, 5, 13, 14} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 5, 14} ∨
        polygon = {0, 3, 4, 5, 13} ∨
        polygon = {0, 2, 5, 13, 14} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 5, 14} ∨
        polygon = {0, 2, 4, 5, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 5, 14} ∨
        polygon = {0, 2, 3, 5, 13} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 5} ∨
        polygon = {0, 1, 5, 13, 14} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 5, 14} ∨
        polygon = {0, 1, 4, 5, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 5, 14} ∨
        polygon = {0, 1, 3, 5, 13} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 5} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 5, 14} ∨
        polygon = {0, 1, 2, 5, 13} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 5} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 5} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24639] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask00735 :
    (({0, 1, 2, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 9}, {2, 4, 6, 7, 9}, {2, 3, 6, 7, 9}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {1, 4, 6, 7, 9}, {1, 3, 6, 7, 9}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {1, 2, 6, 7, 9}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {0, 4, 6, 7, 9}, {0, 3, 6, 7, 9}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}, {0, 2, 6, 7, 9}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 1, 6, 7, 9}, {0, 1, 4, 7, 9}, {0, 1, 4, 6, 9}, {0, 1, 4, 6, 7}, {0, 1, 3, 7, 9}, {0, 1, 3, 6, 9}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 2, 7, 9}, {0, 1, 2, 6, 9}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask00735 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 7, 9} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 2, 6, 7, 9} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 7, 9} ∨
        polygon = {0, 3, 6, 7, 9} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 6, 7, 9} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 7, 9} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask00735] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01247 :
    (({0, 1, 2, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 10}, {2, 4, 6, 7, 10}, {2, 3, 6, 7, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {1, 4, 6, 7, 10}, {1, 3, 6, 7, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {1, 2, 6, 7, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {0, 4, 6, 7, 10}, {0, 3, 6, 7, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}, {0, 2, 6, 7, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 1, 6, 7, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 7}, {0, 1, 3, 7, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 2, 7, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01247 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 7, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 2, 6, 7, 10} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 7, 10} ∨
        polygon = {0, 3, 6, 7, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 6, 7, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 7, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01247] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04319 :
    (({0, 1, 2, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 12}, {2, 4, 6, 7, 12}, {2, 3, 6, 7, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}, {1, 4, 6, 7, 12}, {1, 3, 6, 7, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 7}, {1, 2, 6, 7, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 7}, {1, 2, 3, 7, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {0, 4, 6, 7, 12}, {0, 3, 6, 7, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}, {0, 2, 6, 7, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 1, 6, 7, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 7}, {0, 1, 3, 7, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 2, 7, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04319 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 7, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 2, 6, 7, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 7, 12} ∨
        polygon = {0, 3, 6, 7, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 6, 7, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 7, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04319] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08415 :
    (({0, 1, 2, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 13}, {2, 4, 6, 7, 13}, {2, 3, 6, 7, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 7}, {1, 4, 6, 7, 13}, {1, 3, 6, 7, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 7}, {1, 2, 6, 7, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 7}, {1, 2, 3, 7, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {0, 4, 6, 7, 13}, {0, 3, 6, 7, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 7}, {0, 2, 6, 7, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 7}, {0, 2, 3, 7, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 1, 6, 7, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 7}, {0, 1, 3, 7, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 2, 7, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08415 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 7, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 2, 6, 7, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 7, 13} ∨
        polygon = {0, 3, 6, 7, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 6, 7, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 7, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08415] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16607 :
    (({0, 1, 2, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 14}, {2, 4, 6, 7, 14}, {2, 3, 6, 7, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 7}, {1, 4, 6, 7, 14}, {1, 3, 6, 7, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 7}, {1, 2, 6, 7, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 7}, {1, 2, 3, 7, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {0, 4, 6, 7, 14}, {0, 3, 6, 7, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 7}, {0, 2, 6, 7, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 7}, {0, 2, 3, 7, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 7}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 7}, {0, 2, 3, 4, 6}, {0, 1, 6, 7, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 7}, {0, 1, 3, 7, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 7}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 7}, {0, 1, 3, 4, 6}, {0, 1, 2, 7, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 7}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 7}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16607 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 7, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 7, 14} ∨
        polygon = {0, 3, 6, 7, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 7} ∨
        polygon = {0, 2, 6, 7, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 7} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 7} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 7, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 7} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 7} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 7} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16607] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01631 :
    (({0, 1, 2, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 10}, {2, 4, 6, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {1, 4, 6, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 2, 6, 9, 10}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {0, 4, 6, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}, {0, 2, 6, 9, 10}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 1, 6, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 4, 6, 10}, {0, 1, 4, 6, 9}, {0, 1, 3, 9, 10}, {0, 1, 3, 6, 10}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 2, 9, 10}, {0, 1, 2, 6, 10}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01631 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 2, 6, 9, 10} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 9, 10} ∨
        polygon = {0, 3, 6, 9, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 6, 9, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 9, 10} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01631] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04703 :
    (({0, 1, 2, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 12}, {2, 4, 6, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {1, 4, 6, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 2, 6, 9, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {0, 4, 6, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}, {0, 2, 6, 9, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 1, 6, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 9}, {0, 1, 3, 9, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 2, 9, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04703 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 2, 6, 9, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 9, 12} ∨
        polygon = {0, 3, 6, 9, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 6, 9, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 9, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04703] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08799 :
    (({0, 1, 2, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 13}, {2, 4, 6, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {1, 4, 6, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}, {1, 2, 6, 9, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 3, 9, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {0, 4, 6, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}, {0, 2, 6, 9, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}, {0, 2, 3, 9, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 1, 6, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 9}, {0, 1, 3, 9, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 2, 9, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08799 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 9, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 2, 6, 9, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 9, 13} ∨
        polygon = {0, 3, 6, 9, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 6, 9, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 9, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08799] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16991 :
    (({0, 1, 2, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 14}, {2, 4, 6, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 9}, {1, 4, 6, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 9}, {1, 2, 6, 9, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 9}, {1, 2, 3, 9, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 9}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {0, 4, 6, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 9}, {0, 2, 6, 9, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 9}, {0, 2, 3, 9, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 6}, {0, 1, 6, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 9}, {0, 1, 3, 9, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 6}, {0, 1, 2, 9, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16991 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 9, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 2, 6, 9, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 9} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 9, 14} ∨
        polygon = {0, 3, 6, 9, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 9} ∨
        polygon = {0, 2, 6, 9, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 9} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 9, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 9} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16991] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05215 :
    (({0, 1, 2, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 12}, {2, 4, 6, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {1, 4, 6, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 2, 6, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}, {0, 4, 6, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}, {0, 2, 6, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}, {0, 1, 6, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 6, 12}, {0, 1, 4, 6, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 6, 12}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}, {0, 1, 2, 10, 12}, {0, 1, 2, 6, 12}, {0, 1, 2, 6, 10}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05215 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 2, 6, 10, 12} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 10, 12} ∨
        polygon = {0, 3, 6, 10, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 2, 6, 10, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 10, 12} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05215] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09311 :
    (({0, 1, 2, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 13}, {2, 4, 6, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {1, 4, 6, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 2, 6, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}, {0, 4, 6, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}, {0, 2, 6, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}, {0, 1, 6, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}, {0, 1, 2, 10, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09311 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 2, 6, 10, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 10, 13} ∨
        polygon = {0, 3, 6, 10, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 2, 6, 10, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 10, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09311] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17503 :
    (({0, 1, 2, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 14}, {2, 4, 6, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {1, 4, 6, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}, {1, 2, 6, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}, {0, 4, 6, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}, {0, 2, 6, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 6}, {0, 1, 6, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 6}, {0, 1, 2, 10, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17503 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 2, 6, 10, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 10, 14} ∨
        polygon = {0, 3, 6, 10, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 10} ∨
        polygon = {0, 2, 6, 10, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 10, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17503] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12383 :
    (({0, 1, 2, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 13}, {2, 4, 6, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {1, 4, 6, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 2, 6, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 6}, {0, 4, 6, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}, {0, 2, 6, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 6}, {0, 1, 6, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 6, 13}, {0, 1, 4, 6, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 6, 13}, {0, 1, 3, 6, 12}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 6}, {0, 1, 2, 12, 13}, {0, 1, 2, 6, 13}, {0, 1, 2, 6, 12}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12383 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 2, 6, 12, 13} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 12, 13} ∨
        polygon = {0, 3, 6, 12, 13} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 2, 6, 12, 13} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 12, 13} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12383] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20575 :
    (({0, 1, 2, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 14}, {2, 4, 6, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {1, 4, 6, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 2, 6, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 6}, {0, 4, 6, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}, {0, 2, 6, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 6}, {0, 1, 6, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 6}, {0, 1, 2, 12, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20575 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 2, 6, 12, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 12, 14} ∨
        polygon = {0, 3, 6, 12, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 12} ∨
        polygon = {0, 2, 6, 12, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 12, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20575] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24671 :
    (({0, 1, 2, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 13, 14}, {2, 4, 6, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {1, 4, 6, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 2, 6, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 6}, {0, 4, 6, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}, {0, 2, 6, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 6}, {0, 1, 6, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 6, 14}, {0, 1, 4, 6, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 6, 14}, {0, 1, 3, 6, 13}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 6}, {0, 1, 2, 13, 14}, {0, 1, 2, 6, 14}, {0, 1, 2, 6, 13}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 6}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 6}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24671 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 6, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 2, 6, 13, 14} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {0, 4, 6, 13, 14} ∨
        polygon = {0, 3, 6, 13, 14} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 6, 14} ∨
        polygon = {0, 3, 4, 6, 13} ∨
        polygon = {0, 2, 6, 13, 14} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 6, 14} ∨
        polygon = {0, 2, 4, 6, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 6, 14} ∨
        polygon = {0, 2, 3, 6, 13} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 6} ∨
        polygon = {0, 1, 6, 13, 14} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 6, 14} ∨
        polygon = {0, 1, 4, 6, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 6, 14} ∨
        polygon = {0, 1, 3, 6, 13} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 6} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 6, 14} ∨
        polygon = {0, 1, 2, 6, 13} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 6} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 6} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24671] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01695 :
    (({0, 1, 2, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 3, 7, 9, 10}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {1, 4, 7, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 2, 7, 9, 10}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {0, 4, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}, {0, 2, 7, 9, 10}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 1, 7, 9, 10}, {0, 1, 4, 9, 10}, {0, 1, 4, 7, 10}, {0, 1, 4, 7, 9}, {0, 1, 3, 9, 10}, {0, 1, 3, 7, 10}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 2, 9, 10}, {0, 1, 2, 7, 10}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01695 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 2, 7, 9, 10} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 9, 10} ∨
        polygon = {0, 3, 7, 9, 10} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 7, 9, 10} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 9, 10} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01695] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04767 :
    (({0, 1, 2, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 3, 7, 9, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {1, 4, 7, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 2, 7, 9, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {0, 4, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}, {0, 2, 7, 9, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 1, 7, 9, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 9}, {0, 1, 3, 9, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 2, 9, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04767 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 2, 7, 9, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 9, 12} ∨
        polygon = {0, 3, 7, 9, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 7, 9, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 9, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04767] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08863 :
    (({0, 1, 2, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 3, 7, 9, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {1, 4, 7, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 2, 7, 9, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {0, 4, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}, {0, 2, 7, 9, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 1, 7, 9, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 9}, {0, 1, 3, 9, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 2, 9, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08863 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 2, 7, 9, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 9, 13} ∨
        polygon = {0, 3, 7, 9, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 7, 9, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 9, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08863] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17055 :
    (({0, 1, 2, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 3, 7, 9, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 9}, {1, 4, 7, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 9}, {1, 2, 7, 9, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 9}, {1, 2, 3, 9, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 9}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {0, 4, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}, {0, 2, 7, 9, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 9}, {0, 2, 3, 9, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 9}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 9}, {0, 2, 3, 4, 7}, {0, 1, 7, 9, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 9}, {0, 1, 3, 9, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 9}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 9}, {0, 1, 3, 4, 7}, {0, 1, 2, 9, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 9}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 9}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17055 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 2, 7, 9, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 9} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 9, 14} ∨
        polygon = {0, 3, 7, 9, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 9} ∨
        polygon = {0, 2, 7, 9, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 9} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 9} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 9, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 9} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 9} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 9} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17055] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05279 :
    (({0, 1, 2, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {1, 4, 7, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 2, 7, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {0, 4, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}, {0, 2, 7, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 1, 7, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 7, 12}, {0, 1, 4, 7, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 7, 12}, {0, 1, 3, 7, 10}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 2, 10, 12}, {0, 1, 2, 7, 12}, {0, 1, 2, 7, 10}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05279 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 2, 7, 10, 12} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 10, 12} ∨
        polygon = {0, 3, 7, 10, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 2, 7, 10, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 10, 12} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05279] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09375 :
    (({0, 1, 2, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {1, 4, 7, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 2, 7, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {0, 4, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}, {0, 2, 7, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 1, 7, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 2, 10, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09375 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 2, 7, 10, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 10, 13} ∨
        polygon = {0, 3, 7, 10, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 2, 7, 10, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 10, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09375] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17567 :
    (({0, 1, 2, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {1, 4, 7, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}, {1, 2, 7, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {0, 4, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}, {0, 2, 7, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 7}, {0, 1, 7, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 7}, {0, 1, 2, 10, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17567 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 2, 7, 10, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 10, 14} ∨
        polygon = {0, 3, 7, 10, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 10} ∨
        polygon = {0, 2, 7, 10, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 10, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17567] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12447 :
    (({0, 1, 2, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {1, 4, 7, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 2, 7, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}, {0, 4, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}, {0, 2, 7, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 1, 7, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 7, 13}, {0, 1, 4, 7, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 7, 13}, {0, 1, 3, 7, 12}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 2, 12, 13}, {0, 1, 2, 7, 13}, {0, 1, 2, 7, 12}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12447 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 2, 7, 12, 13} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 12, 13} ∨
        polygon = {0, 3, 7, 12, 13} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 2, 7, 12, 13} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 12, 13} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12447] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20639 :
    (({0, 1, 2, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {1, 4, 7, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 2, 7, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}, {0, 4, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}, {0, 2, 7, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 7}, {0, 1, 7, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 7}, {0, 1, 2, 12, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20639 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 2, 7, 12, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 12, 14} ∨
        polygon = {0, 3, 7, 12, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 12} ∨
        polygon = {0, 2, 7, 12, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 12, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20639] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24735 :
    (({0, 1, 2, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {1, 4, 7, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 2, 7, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 7}, {0, 4, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}, {0, 2, 7, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 7}, {0, 1, 7, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 7, 14}, {0, 1, 4, 7, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 7, 14}, {0, 1, 3, 7, 13}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 7}, {0, 1, 2, 13, 14}, {0, 1, 2, 7, 14}, {0, 1, 2, 7, 13}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 7}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 7}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24735 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 2, 7, 13, 14} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {0, 4, 7, 13, 14} ∨
        polygon = {0, 3, 7, 13, 14} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 7, 14} ∨
        polygon = {0, 3, 4, 7, 13} ∨
        polygon = {0, 2, 7, 13, 14} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 7, 14} ∨
        polygon = {0, 2, 4, 7, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 7, 14} ∨
        polygon = {0, 2, 3, 7, 13} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 7} ∨
        polygon = {0, 1, 7, 13, 14} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 7, 14} ∨
        polygon = {0, 1, 4, 7, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 7, 14} ∨
        polygon = {0, 1, 3, 7, 13} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 7} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 7, 14} ∨
        polygon = {0, 1, 2, 7, 13} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 7} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 7} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24735] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05663 :
    (({0, 1, 2, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {1, 4, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 2, 9, 10, 12}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {0, 4, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}, {0, 2, 9, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 1, 9, 10, 12}, {0, 1, 4, 10, 12}, {0, 1, 4, 9, 12}, {0, 1, 4, 9, 10}, {0, 1, 3, 10, 12}, {0, 1, 3, 9, 12}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 2, 10, 12}, {0, 1, 2, 9, 12}, {0, 1, 2, 9, 10}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05663 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 2, 9, 10, 12} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {0, 4, 9, 10, 12} ∨
        polygon = {0, 3, 9, 10, 12} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 2, 9, 10, 12} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 1, 9, 10, 12} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05663] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09759 :
    (({0, 1, 2, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {1, 4, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 2, 9, 10, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {0, 4, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}, {0, 2, 9, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 1, 9, 10, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 10}, {0, 1, 3, 10, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 2, 10, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 10}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09759 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 2, 9, 10, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {0, 4, 9, 10, 13} ∨
        polygon = {0, 3, 9, 10, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 2, 9, 10, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 1, 9, 10, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09759] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17951 :
    (({0, 1, 2, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {1, 4, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 10}, {1, 2, 9, 10, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {0, 4, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}, {0, 2, 9, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}, {0, 2, 3, 4, 9}, {0, 1, 9, 10, 14}, {0, 1, 4, 10, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 10}, {0, 1, 3, 10, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 10}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 10}, {0, 1, 3, 4, 9}, {0, 1, 2, 10, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 10}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 10}, {0, 1, 2, 4, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17951 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 2, 9, 10, 14} ∨
        polygon = {1, 2, 4, 10, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 10} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {0, 4, 9, 10, 14} ∨
        polygon = {0, 3, 9, 10, 14} ∨
        polygon = {0, 3, 4, 10, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 10} ∨
        polygon = {0, 2, 9, 10, 14} ∨
        polygon = {0, 2, 4, 10, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 10} ∨
        polygon = {0, 2, 3, 10, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 10} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 1, 9, 10, 14} ∨
        polygon = {0, 1, 4, 10, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 10} ∨
        polygon = {0, 1, 3, 10, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 10} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 2, 10, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 10} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17951] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12831 :
    (({0, 1, 2, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {1, 4, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 2, 9, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {0, 4, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}, {0, 2, 9, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 1, 9, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 9, 13}, {0, 1, 4, 9, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 9, 13}, {0, 1, 3, 9, 12}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 2, 12, 13}, {0, 1, 2, 9, 13}, {0, 1, 2, 9, 12}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12831 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 2, 9, 12, 13} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {0, 4, 9, 12, 13} ∨
        polygon = {0, 3, 9, 12, 13} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 2, 9, 12, 13} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 1, 9, 12, 13} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12831] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21023 :
    (({0, 1, 2, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {1, 4, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 2, 9, 12, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {0, 4, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}, {0, 2, 9, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 9}, {0, 1, 9, 12, 14}, {0, 1, 4, 12, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 12}, {0, 1, 3, 12, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 12}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 9}, {0, 1, 2, 12, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 12}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21023 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 2, 9, 12, 14} ∨
        polygon = {1, 2, 4, 12, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 12} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {0, 4, 9, 12, 14} ∨
        polygon = {0, 3, 9, 12, 14} ∨
        polygon = {0, 3, 4, 12, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 12} ∨
        polygon = {0, 2, 9, 12, 14} ∨
        polygon = {0, 2, 4, 12, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 12} ∨
        polygon = {0, 2, 3, 12, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 12} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 1, 9, 12, 14} ∨
        polygon = {0, 1, 4, 12, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 12} ∨
        polygon = {0, 1, 3, 12, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 12} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 2, 12, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 12} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21023] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25119 :
    (({0, 1, 2, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {1, 4, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 2, 9, 13, 14}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {0, 4, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}, {0, 2, 9, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 9}, {0, 1, 9, 13, 14}, {0, 1, 4, 13, 14}, {0, 1, 4, 9, 14}, {0, 1, 4, 9, 13}, {0, 1, 3, 13, 14}, {0, 1, 3, 9, 14}, {0, 1, 3, 9, 13}, {0, 1, 3, 4, 14}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 9}, {0, 1, 2, 13, 14}, {0, 1, 2, 9, 14}, {0, 1, 2, 9, 13}, {0, 1, 2, 4, 14}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 9}, {0, 1, 2, 3, 14}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 9}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25119 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 2, 9, 13, 14} ∨
        polygon = {1, 2, 4, 13, 14} ∨
        polygon = {1, 2, 4, 9, 14} ∨
        polygon = {1, 2, 4, 9, 13} ∨
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {0, 4, 9, 13, 14} ∨
        polygon = {0, 3, 9, 13, 14} ∨
        polygon = {0, 3, 4, 13, 14} ∨
        polygon = {0, 3, 4, 9, 14} ∨
        polygon = {0, 3, 4, 9, 13} ∨
        polygon = {0, 2, 9, 13, 14} ∨
        polygon = {0, 2, 4, 13, 14} ∨
        polygon = {0, 2, 4, 9, 14} ∨
        polygon = {0, 2, 4, 9, 13} ∨
        polygon = {0, 2, 3, 13, 14} ∨
        polygon = {0, 2, 3, 9, 14} ∨
        polygon = {0, 2, 3, 9, 13} ∨
        polygon = {0, 2, 3, 4, 14} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 9} ∨
        polygon = {0, 1, 9, 13, 14} ∨
        polygon = {0, 1, 4, 13, 14} ∨
        polygon = {0, 1, 4, 9, 14} ∨
        polygon = {0, 1, 4, 9, 13} ∨
        polygon = {0, 1, 3, 13, 14} ∨
        polygon = {0, 1, 3, 9, 14} ∨
        polygon = {0, 1, 3, 9, 13} ∨
        polygon = {0, 1, 3, 4, 14} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 9} ∨
        polygon = {0, 1, 2, 13, 14} ∨
        polygon = {0, 1, 2, 9, 14} ∨
        polygon = {0, 1, 2, 9, 13} ∨
        polygon = {0, 1, 2, 4, 14} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 9} ∨
        polygon = {0, 1, 2, 3, 14} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 9} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25119] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13343 :
    (({0, 1, 2, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {1, 4, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 2, 10, 12, 13}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {0, 4, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}, {0, 2, 10, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}, {0, 2, 3, 4, 10}, {0, 1, 10, 12, 13}, {0, 1, 4, 12, 13}, {0, 1, 4, 10, 13}, {0, 1, 4, 10, 12}, {0, 1, 3, 12, 13}, {0, 1, 3, 10, 13}, {0, 1, 3, 10, 12}, {0, 1, 3, 4, 13}, {0, 1, 3, 4, 12}, {0, 1, 3, 4, 10}, {0, 1, 2, 12, 13}, {0, 1, 2, 10, 13}, {0, 1, 2, 10, 12}, {0, 1, 2, 4, 13}, {0, 1, 2, 4, 12}, {0, 1, 2, 4, 10}, {0, 1, 2, 3, 13}, {0, 1, 2, 3, 12}, {0, 1, 2, 3, 10}, {0, 1, 2, 3, 4}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13343 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {0, 1, 2, 3, 4, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 2, 10, 12, 13} ∨
        polygon = {1, 2, 4, 12, 13} ∨
        polygon = {1, 2, 4, 10, 13} ∨
        polygon = {1, 2, 4, 10, 12} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {0, 4, 10, 12, 13} ∨
        polygon = {0, 3, 10, 12, 13} ∨
        polygon = {0, 3, 4, 12, 13} ∨
        polygon = {0, 3, 4, 10, 13} ∨
        polygon = {0, 3, 4, 10, 12} ∨
        polygon = {0, 2, 10, 12, 13} ∨
        polygon = {0, 2, 4, 12, 13} ∨
        polygon = {0, 2, 4, 10, 13} ∨
        polygon = {0, 2, 4, 10, 12} ∨
        polygon = {0, 2, 3, 12, 13} ∨
        polygon = {0, 2, 3, 10, 13} ∨
        polygon = {0, 2, 3, 10, 12} ∨
        polygon = {0, 2, 3, 4, 13} ∨
        polygon = {0, 2, 3, 4, 12} ∨
        polygon = {0, 2, 3, 4, 10} ∨
        polygon = {0, 1, 10, 12, 13} ∨
        polygon = {0, 1, 4, 12, 13} ∨
        polygon = {0, 1, 4, 10, 13} ∨
        polygon = {0, 1, 4, 10, 12} ∨
        polygon = {0, 1, 3, 12, 13} ∨
        polygon = {0, 1, 3, 10, 13} ∨
        polygon = {0, 1, 3, 10, 12} ∨
        polygon = {0, 1, 3, 4, 13} ∨
        polygon = {0, 1, 3, 4, 12} ∨
        polygon = {0, 1, 3, 4, 10} ∨
        polygon = {0, 1, 2, 12, 13} ∨
        polygon = {0, 1, 2, 10, 13} ∨
        polygon = {0, 1, 2, 10, 12} ∨
        polygon = {0, 1, 2, 4, 13} ∨
        polygon = {0, 1, 2, 4, 12} ∨
        polygon = {0, 1, 2, 4, 10} ∨
        polygon = {0, 1, 2, 3, 13} ∨
        polygon = {0, 1, 2, 3, 12} ∨
        polygon = {0, 1, 2, 3, 10} ∨
        polygon = {0, 1, 2, 3, 4} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({0, 1, 2, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13343] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
