module

public import ErdosSzekeres.Fin15AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic helper facts in bounded group 093. -/

theorem fin15Anchored_fiveFamily_mask08446 :
    (({1, 2, 3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {3, 5, 6, 7, 13}, {3, 4, 6, 7, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 13}, {2, 4, 6, 7, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {1, 5, 6, 7, 13}, {1, 4, 6, 7, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {1, 2, 6, 7, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {1, 2, 3, 7, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08446 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 7, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 13} ∨
        polygon = {3, 5, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08446] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16638 :
    (({1, 2, 3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {3, 5, 6, 7, 14}, {3, 4, 6, 7, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 7}, {2, 5, 6, 7, 14}, {2, 4, 6, 7, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 7}, {2, 3, 6, 7, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 7}, {2, 3, 4, 7, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}, {1, 5, 6, 7, 14}, {1, 4, 6, 7, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 7}, {1, 3, 6, 7, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 7}, {1, 3, 4, 7, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 7}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 7}, {1, 3, 4, 5, 6}, {1, 2, 6, 7, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 7}, {1, 2, 4, 7, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 7}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 7}, {1, 2, 4, 5, 6}, {1, 2, 3, 7, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 7}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 7}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16638 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 7, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 7, 14} ∨
        polygon = {3, 5, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 7} ∨
        polygon = {2, 5, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 7} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 7} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 7} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 7} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 7} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16638] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01662 :
    (({1, 2, 3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {3, 5, 6, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 6, 10}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 6, 10}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {1, 5, 6, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {1, 2, 6, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 6, 10}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 10}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {1, 2, 3, 9, 10}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01662 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 10} ∨
        polygon = {3, 5, 6, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 9, 10} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01662] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04734 :
    (({1, 2, 3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {3, 5, 6, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {1, 5, 6, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {1, 2, 6, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {1, 2, 3, 9, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04734 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 12} ∨
        polygon = {3, 5, 6, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 9, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04734] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08830 :
    (({1, 2, 3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {3, 5, 6, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {1, 5, 6, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {1, 2, 6, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {1, 2, 3, 9, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08830 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 13} ∨
        polygon = {3, 5, 6, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 9, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08830] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17022 :
    (({1, 2, 3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {3, 5, 6, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 9}, {2, 5, 6, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 9}, {2, 3, 6, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 9}, {2, 3, 4, 9, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}, {1, 5, 6, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 9}, {1, 3, 6, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 9}, {1, 3, 4, 9, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 9}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 6}, {1, 2, 6, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 9}, {1, 2, 4, 9, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 6}, {1, 2, 3, 9, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17022 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 9, 14} ∨
        polygon = {3, 5, 6, 9, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 9} ∨
        polygon = {2, 5, 6, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 9} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 9} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 9, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 9} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 9} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17022] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05246 :
    (({1, 2, 3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {3, 5, 6, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 6, 12}, {3, 4, 5, 6, 10}, {2, 5, 6, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 6, 12}, {2, 4, 5, 6, 10}, {2, 3, 6, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}, {1, 5, 6, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}, {1, 3, 6, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}, {1, 2, 6, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 6, 12}, {1, 2, 5, 6, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {1, 2, 3, 10, 12}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05246 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 12} ∨
        polygon = {3, 5, 6, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {2, 5, 6, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05246] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09342 :
    (({1, 2, 3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {3, 5, 6, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 10}, {2, 5, 6, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 10}, {2, 3, 6, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}, {1, 5, 6, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}, {1, 3, 6, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}, {1, 2, 6, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {1, 2, 3, 10, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09342 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 13} ∨
        polygon = {3, 5, 6, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {2, 5, 6, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09342] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17534 :
    (({1, 2, 3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {3, 5, 6, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 10}, {2, 5, 6, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 10}, {2, 3, 6, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}, {1, 5, 6, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}, {1, 3, 6, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 6}, {1, 2, 6, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 6}, {1, 2, 3, 10, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17534 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 10, 14} ∨
        polygon = {3, 5, 6, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 10} ∨
        polygon = {2, 5, 6, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 10} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 10} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17534] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12414 :
    (({1, 2, 3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {3, 5, 6, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 6, 13}, {3, 4, 5, 6, 12}, {2, 5, 6, 12, 13}, {2, 4, 6, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 6, 13}, {2, 4, 5, 6, 12}, {2, 3, 6, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 6}, {1, 5, 6, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}, {1, 3, 6, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 6}, {1, 2, 6, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 6, 13}, {1, 2, 5, 6, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 6}, {1, 2, 3, 12, 13}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12414 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 13} ∨
        polygon = {3, 5, 6, 12, 13} ∨
        polygon = {3, 4, 6, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {2, 5, 6, 12, 13} ∨
        polygon = {2, 4, 6, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 3, 6, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 12, 13} ∨
        polygon = {1, 4, 6, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 3, 6, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12414] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20606 :
    (({1, 2, 3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {3, 5, 6, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 12}, {2, 5, 6, 12, 14}, {2, 4, 6, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 12}, {2, 3, 6, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 6}, {1, 5, 6, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}, {1, 3, 6, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 6}, {1, 2, 6, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 6}, {1, 2, 3, 12, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20606 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 12, 14} ∨
        polygon = {3, 5, 6, 12, 14} ∨
        polygon = {3, 4, 6, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 12} ∨
        polygon = {2, 5, 6, 12, 14} ∨
        polygon = {2, 4, 6, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 12} ∨
        polygon = {2, 3, 6, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 12, 14} ∨
        polygon = {1, 4, 6, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 12} ∨
        polygon = {1, 3, 6, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20606] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24702 :
    (({1, 2, 3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {3, 5, 6, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 6, 14}, {3, 4, 5, 6, 13}, {2, 5, 6, 13, 14}, {2, 4, 6, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 6, 14}, {2, 4, 5, 6, 13}, {2, 3, 6, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 6}, {1, 5, 6, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}, {1, 3, 6, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 6}, {1, 2, 6, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 6, 14}, {1, 2, 5, 6, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 6}, {1, 2, 3, 13, 14}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 6}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 6}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24702 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 6, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 6, 13, 14} ∨
        polygon = {3, 5, 6, 13, 14} ∨
        polygon = {3, 4, 6, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 6, 14} ∨
        polygon = {3, 4, 5, 6, 13} ∨
        polygon = {2, 5, 6, 13, 14} ∨
        polygon = {2, 4, 6, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 6, 14} ∨
        polygon = {2, 4, 5, 6, 13} ∨
        polygon = {2, 3, 6, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 6, 14} ∨
        polygon = {2, 3, 5, 6, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 6} ∨
        polygon = {1, 5, 6, 13, 14} ∨
        polygon = {1, 4, 6, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 6, 14} ∨
        polygon = {1, 4, 5, 6, 13} ∨
        polygon = {1, 3, 6, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 6, 14} ∨
        polygon = {1, 3, 5, 6, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 6} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 6} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 6} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24702] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01726 :
    (({1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 5, 9, 10}, {3, 4, 5, 7, 10}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 5, 9, 10}, {2, 4, 5, 7, 10}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {1, 5, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {1, 2, 7, 9, 10}, {1, 2, 5, 9, 10}, {1, 2, 5, 7, 10}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01726 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 10} ∨
        polygon = {3, 5, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01726] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04798 :
    (({1, 2, 3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {1, 5, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {1, 2, 7, 9, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04798 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 12} ∨
        polygon = {3, 5, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04798] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08894 :
    (({1, 2, 3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {1, 5, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {1, 2, 7, 9, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08894 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 13} ∨
        polygon = {3, 5, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08894] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17086 :
    (({1, 2, 3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 9}, {2, 5, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 9}, {2, 3, 7, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 9}, {2, 3, 4, 9, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}, {1, 5, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 9}, {1, 3, 7, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 9}, {1, 3, 4, 9, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 9}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 9}, {1, 3, 4, 5, 7}, {1, 2, 7, 9, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 9}, {1, 2, 4, 9, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 9}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 9}, {1, 2, 4, 5, 7}, {1, 2, 3, 9, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 9}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 9}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17086 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 9, 14} ∨
        polygon = {3, 5, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 9} ∨
        polygon = {2, 5, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 9} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 9} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 9} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 9} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 9} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17086] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05310 :
    (({1, 2, 3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 7, 12}, {3, 4, 5, 7, 10}, {2, 5, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 7, 12}, {2, 4, 5, 7, 10}, {2, 3, 7, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 7, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {1, 5, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}, {1, 3, 7, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {1, 2, 7, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 7, 12}, {1, 2, 5, 7, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05310 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 12} ∨
        polygon = {3, 5, 7, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 5, 7, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05310] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09406 :
    (({1, 2, 3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 10}, {2, 5, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 10}, {2, 3, 7, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {1, 5, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}, {1, 3, 7, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {1, 2, 7, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09406 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 13} ∨
        polygon = {3, 5, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 5, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09406] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17598 :
    (({1, 2, 3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 10}, {2, 5, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 10}, {2, 3, 7, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}, {1, 5, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}, {1, 3, 7, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 7}, {1, 2, 7, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 7}, {1, 2, 3, 10, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17598 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 10, 14} ∨
        polygon = {3, 5, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 10} ∨
        polygon = {2, 5, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 10} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 10} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17598] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12478 :
    (({1, 2, 3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 7, 13}, {3, 4, 5, 7, 12}, {2, 5, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 7, 13}, {2, 4, 5, 7, 12}, {2, 3, 7, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 7, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {1, 5, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}, {1, 3, 7, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}, {1, 2, 7, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 7, 13}, {1, 2, 5, 7, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {1, 2, 3, 12, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12478 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 13} ∨
        polygon = {3, 5, 7, 12, 13} ∨
        polygon = {3, 4, 7, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {2, 5, 7, 12, 13} ∨
        polygon = {2, 4, 7, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 3, 7, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 12, 13} ∨
        polygon = {1, 4, 7, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 3, 7, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12478] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask20670 :
    (({1, 2, 3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 12}, {2, 5, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 12}, {2, 3, 7, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}, {1, 5, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}, {1, 3, 7, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 7}, {1, 2, 7, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 7}, {1, 2, 3, 12, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask20670 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 12, 14} ∨
        polygon = {3, 5, 7, 12, 14} ∨
        polygon = {3, 4, 7, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 12} ∨
        polygon = {2, 5, 7, 12, 14} ∨
        polygon = {2, 4, 7, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 12} ∨
        polygon = {2, 3, 7, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 12, 14} ∨
        polygon = {1, 4, 7, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 12} ∨
        polygon = {1, 3, 7, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask20670] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask24766 :
    (({1, 2, 3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 7, 14}, {3, 4, 5, 7, 13}, {2, 5, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 7, 14}, {2, 4, 5, 7, 13}, {2, 3, 7, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 7, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 7}, {1, 5, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}, {1, 3, 7, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 7}, {1, 2, 7, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 7, 14}, {1, 2, 5, 7, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 7}, {1, 2, 3, 13, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask24766 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 7, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 7, 13, 14} ∨
        polygon = {3, 5, 7, 13, 14} ∨
        polygon = {3, 4, 7, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 7, 14} ∨
        polygon = {3, 4, 5, 7, 13} ∨
        polygon = {2, 5, 7, 13, 14} ∨
        polygon = {2, 4, 7, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 7, 14} ∨
        polygon = {2, 4, 5, 7, 13} ∨
        polygon = {2, 3, 7, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 7, 14} ∨
        polygon = {2, 3, 5, 7, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 7} ∨
        polygon = {1, 5, 7, 13, 14} ∨
        polygon = {1, 4, 7, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 7, 14} ∨
        polygon = {1, 4, 5, 7, 13} ∨
        polygon = {1, 3, 7, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 7, 14} ∨
        polygon = {1, 3, 5, 7, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 7} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask24766] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05694 :
    (({1, 2, 3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 5, 10, 12}, {3, 4, 5, 9, 12}, {3, 4, 5, 9, 10}, {2, 5, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 4, 5, 10, 12}, {2, 4, 5, 9, 12}, {2, 4, 5, 9, 10}, {2, 3, 9, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 9, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {1, 5, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}, {1, 3, 9, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 2, 9, 10, 12}, {1, 2, 5, 10, 12}, {1, 2, 5, 9, 12}, {1, 2, 5, 9, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 9, 12}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 3, 10, 12}, {1, 2, 3, 9, 12}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05694 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 9, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 12} ∨
        polygon = {3, 5, 9, 10, 12} ∨
        polygon = {3, 4, 9, 10, 12} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 5, 9, 10, 12} ∨
        polygon = {2, 4, 9, 10, 12} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 3, 9, 10, 12} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 5, 9, 10, 12} ∨
        polygon = {1, 4, 9, 10, 12} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 3, 9, 10, 12} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05694] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09790 :
    (({1, 2, 3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 10}, {2, 5, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 10}, {2, 3, 9, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {1, 5, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}, {1, 3, 9, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 2, 9, 10, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 3, 10, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09790 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 9, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 13} ∨
        polygon = {3, 5, 9, 10, 13} ∨
        polygon = {3, 4, 9, 10, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 5, 9, 10, 13} ∨
        polygon = {2, 4, 9, 10, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 3, 9, 10, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 5, 9, 10, 13} ∨
        polygon = {1, 4, 9, 10, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 3, 9, 10, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09790] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17982 :
    (({1, 2, 3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 10}, {2, 5, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 10}, {2, 3, 9, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}, {1, 5, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}, {1, 3, 9, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 10}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}, {1, 3, 4, 5, 9}, {1, 2, 9, 10, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 10}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 10}, {1, 2, 4, 5, 9}, {1, 2, 3, 10, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 10}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 10}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17982 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 9, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 10, 14} ∨
        polygon = {3, 5, 9, 10, 14} ∨
        polygon = {3, 4, 9, 10, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 10} ∨
        polygon = {2, 5, 9, 10, 14} ∨
        polygon = {2, 4, 9, 10, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 10} ∨
        polygon = {2, 3, 9, 10, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 5, 9, 10, 14} ∨
        polygon = {1, 4, 9, 10, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 10} ∨
        polygon = {1, 3, 9, 10, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 10} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17982] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask12862 :
    (({1, 2, 3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 9, 13}, {3, 4, 5, 9, 12}, {2, 5, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 9, 13}, {2, 4, 5, 9, 12}, {2, 3, 9, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 9, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {1, 5, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}, {1, 3, 9, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 2, 9, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 9, 13}, {1, 2, 5, 9, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 9, 13}, {1, 2, 4, 9, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 3, 12, 13}, {1, 2, 3, 9, 13}, {1, 2, 3, 9, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask12862 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 9, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 13} ∨
        polygon = {3, 5, 9, 12, 13} ∨
        polygon = {3, 4, 9, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {2, 5, 9, 12, 13} ∨
        polygon = {2, 4, 9, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 3, 9, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 5, 9, 12, 13} ∨
        polygon = {1, 4, 9, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 3, 9, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask12862] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21054 :
    (({1, 2, 3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 12}, {2, 5, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 12}, {2, 3, 9, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}, {1, 5, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}, {1, 3, 9, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 9}, {1, 2, 9, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 9}, {1, 2, 3, 12, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21054 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 9, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 12, 14} ∨
        polygon = {3, 5, 9, 12, 14} ∨
        polygon = {3, 4, 9, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 12} ∨
        polygon = {2, 5, 9, 12, 14} ∨
        polygon = {2, 4, 9, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 12} ∨
        polygon = {2, 3, 9, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 5, 9, 12, 14} ∨
        polygon = {1, 4, 9, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 12} ∨
        polygon = {1, 3, 9, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21054] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25150 :
    (({1, 2, 3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 9, 14}, {3, 4, 5, 9, 13}, {2, 5, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 9, 14}, {2, 4, 5, 9, 13}, {2, 3, 9, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 9, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}, {1, 5, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}, {1, 3, 9, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 9}, {1, 2, 9, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 9, 14}, {1, 2, 5, 9, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 9, 14}, {1, 2, 4, 9, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 9}, {1, 2, 3, 13, 14}, {1, 2, 3, 9, 14}, {1, 2, 3, 9, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 9}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25150 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 9, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 9, 13, 14} ∨
        polygon = {3, 5, 9, 13, 14} ∨
        polygon = {3, 4, 9, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 9, 14} ∨
        polygon = {3, 4, 5, 9, 13} ∨
        polygon = {2, 5, 9, 13, 14} ∨
        polygon = {2, 4, 9, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 9, 14} ∨
        polygon = {2, 4, 5, 9, 13} ∨
        polygon = {2, 3, 9, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 9, 14} ∨
        polygon = {2, 3, 5, 9, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 9} ∨
        polygon = {1, 5, 9, 13, 14} ∨
        polygon = {1, 4, 9, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 9, 14} ∨
        polygon = {1, 4, 5, 9, 13} ∨
        polygon = {1, 3, 9, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 9, 14} ∨
        polygon = {1, 3, 5, 9, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 9} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 9} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25150] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask13374 :
    (({1, 2, 3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 5, 12, 13}, {3, 4, 5, 10, 13}, {3, 4, 5, 10, 12}, {2, 5, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 4, 5, 12, 13}, {2, 4, 5, 10, 13}, {2, 4, 5, 10, 12}, {2, 3, 10, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 10, 12}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {1, 5, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}, {1, 3, 10, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 2, 10, 12, 13}, {1, 2, 5, 12, 13}, {1, 2, 5, 10, 13}, {1, 2, 5, 10, 12}, {1, 2, 4, 12, 13}, {1, 2, 4, 10, 13}, {1, 2, 4, 10, 12}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 3, 12, 13}, {1, 2, 3, 10, 13}, {1, 2, 3, 10, 12}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask13374 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 10, 12, 13} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 13} ∨
        polygon = {3, 5, 10, 12, 13} ∨
        polygon = {3, 4, 10, 12, 13} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {2, 5, 10, 12, 13} ∨
        polygon = {2, 4, 10, 12, 13} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 3, 10, 12, 13} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {1, 5, 10, 12, 13} ∨
        polygon = {1, 4, 10, 12, 13} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 3, 10, 12, 13} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
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
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask13374] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask21566 :
    (({1, 2, 3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 12}, {2, 5, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 12}, {2, 3, 10, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 12}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}, {1, 5, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}, {1, 3, 10, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}, {1, 3, 4, 5, 10}, {1, 2, 10, 12, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 12}, {1, 2, 4, 12, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 12}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 12}, {1, 2, 4, 5, 10}, {1, 2, 3, 12, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 12}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 12}, {1, 2, 3, 5, 10}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask21566 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 10, 12, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 12, 14} ∨
        polygon = {3, 5, 10, 12, 14} ∨
        polygon = {3, 4, 10, 12, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 12} ∨
        polygon = {2, 5, 10, 12, 14} ∨
        polygon = {2, 4, 10, 12, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 12} ∨
        polygon = {2, 3, 10, 12, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 12} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {1, 5, 10, 12, 14} ∨
        polygon = {1, 4, 10, 12, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 12} ∨
        polygon = {1, 3, 10, 12, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 12} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 12} ∨
        polygon = {1, 3, 4, 5, 10} ∨
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
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask21566] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask25662 :
    (({1, 2, 3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 10, 14}, {3, 4, 5, 10, 13}, {2, 5, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 10, 14}, {2, 4, 5, 10, 13}, {2, 3, 10, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 10, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}, {1, 5, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}, {1, 3, 10, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 10}, {1, 2, 10, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 10, 14}, {1, 2, 5, 10, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 10, 14}, {1, 2, 4, 10, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 10}, {1, 2, 3, 13, 14}, {1, 2, 3, 10, 14}, {1, 2, 3, 10, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 10}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask25662 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 10, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 10, 13, 14} ∨
        polygon = {3, 5, 10, 13, 14} ∨
        polygon = {3, 4, 10, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 10, 14} ∨
        polygon = {3, 4, 5, 10, 13} ∨
        polygon = {2, 5, 10, 13, 14} ∨
        polygon = {2, 4, 10, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 10, 14} ∨
        polygon = {2, 4, 5, 10, 13} ∨
        polygon = {2, 3, 10, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 10, 14} ∨
        polygon = {2, 3, 5, 10, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 10} ∨
        polygon = {1, 5, 10, 13, 14} ∨
        polygon = {1, 4, 10, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 10, 14} ∨
        polygon = {1, 4, 5, 10, 13} ∨
        polygon = {1, 3, 10, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 10, 14} ∨
        polygon = {1, 3, 5, 10, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 10} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 10} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask25662] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask28734 :
    (({1, 2, 3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 5, 13, 14}, {3, 4, 5, 12, 14}, {3, 4, 5, 12, 13}, {2, 5, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 4, 5, 13, 14}, {2, 4, 5, 12, 14}, {2, 4, 5, 12, 13}, {2, 3, 12, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 12, 13}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}, {1, 5, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}, {1, 3, 12, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}, {1, 2, 12, 13, 14}, {1, 2, 5, 13, 14}, {1, 2, 5, 12, 14}, {1, 2, 5, 12, 13}, {1, 2, 4, 13, 14}, {1, 2, 4, 12, 14}, {1, 2, 4, 12, 13}, {1, 2, 4, 5, 14}, {1, 2, 4, 5, 13}, {1, 2, 4, 5, 12}, {1, 2, 3, 13, 14}, {1, 2, 3, 12, 14}, {1, 2, 3, 12, 13}, {1, 2, 3, 5, 14}, {1, 2, 3, 5, 13}, {1, 2, 3, 5, 12}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 5}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask28734 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 5, 12, 13, 14} →
      polygon.card = 5 →
        polygon = {4, 5, 12, 13, 14} ∨
        polygon = {3, 5, 12, 13, 14} ∨
        polygon = {3, 4, 12, 13, 14} ∨
        polygon = {3, 4, 5, 13, 14} ∨
        polygon = {3, 4, 5, 12, 14} ∨
        polygon = {3, 4, 5, 12, 13} ∨
        polygon = {2, 5, 12, 13, 14} ∨
        polygon = {2, 4, 12, 13, 14} ∨
        polygon = {2, 4, 5, 13, 14} ∨
        polygon = {2, 4, 5, 12, 14} ∨
        polygon = {2, 4, 5, 12, 13} ∨
        polygon = {2, 3, 12, 13, 14} ∨
        polygon = {2, 3, 5, 13, 14} ∨
        polygon = {2, 3, 5, 12, 14} ∨
        polygon = {2, 3, 5, 12, 13} ∨
        polygon = {2, 3, 4, 13, 14} ∨
        polygon = {2, 3, 4, 12, 14} ∨
        polygon = {2, 3, 4, 12, 13} ∨
        polygon = {2, 3, 4, 5, 14} ∨
        polygon = {2, 3, 4, 5, 13} ∨
        polygon = {2, 3, 4, 5, 12} ∨
        polygon = {1, 5, 12, 13, 14} ∨
        polygon = {1, 4, 12, 13, 14} ∨
        polygon = {1, 4, 5, 13, 14} ∨
        polygon = {1, 4, 5, 12, 14} ∨
        polygon = {1, 4, 5, 12, 13} ∨
        polygon = {1, 3, 12, 13, 14} ∨
        polygon = {1, 3, 5, 13, 14} ∨
        polygon = {1, 3, 5, 12, 14} ∨
        polygon = {1, 3, 5, 12, 13} ∨
        polygon = {1, 3, 4, 13, 14} ∨
        polygon = {1, 3, 4, 12, 14} ∨
        polygon = {1, 3, 4, 12, 13} ∨
        polygon = {1, 3, 4, 5, 14} ∨
        polygon = {1, 3, 4, 5, 13} ∨
        polygon = {1, 3, 4, 5, 12} ∨
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
        polygon = {1, 2, 3, 13, 14} ∨
        polygon = {1, 2, 3, 12, 14} ∨
        polygon = {1, 2, 3, 12, 13} ∨
        polygon = {1, 2, 3, 5, 14} ∨
        polygon = {1, 2, 3, 5, 13} ∨
        polygon = {1, 2, 3, 5, 12} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 5} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask28734] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask16862 :
    (({1, 2, 3, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 14}, {3, 6, 7, 8, 14}, {3, 4, 7, 8, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 8}, {2, 6, 7, 8, 14}, {2, 4, 7, 8, 14}, {2, 4, 6, 8, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 8}, {2, 3, 7, 8, 14}, {2, 3, 6, 8, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 8}, {2, 3, 4, 8, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 8}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 8}, {2, 3, 4, 6, 7}, {1, 6, 7, 8, 14}, {1, 4, 7, 8, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 8}, {1, 3, 7, 8, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 8}, {1, 3, 4, 8, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 8}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 8}, {1, 3, 4, 6, 7}, {1, 2, 7, 8, 14}, {1, 2, 6, 8, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 8}, {1, 2, 4, 8, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 8}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 8}, {1, 2, 4, 6, 7}, {1, 2, 3, 8, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 8}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 8}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 8}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask16862 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 8, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 8, 14} ∨
        polygon = {3, 6, 7, 8, 14} ∨
        polygon = {3, 4, 7, 8, 14} ∨
        polygon = {3, 4, 6, 8, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 8} ∨
        polygon = {2, 6, 7, 8, 14} ∨
        polygon = {2, 4, 7, 8, 14} ∨
        polygon = {2, 4, 6, 8, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 8} ∨
        polygon = {2, 3, 7, 8, 14} ∨
        polygon = {2, 3, 6, 8, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 8} ∨
        polygon = {2, 3, 4, 8, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 8} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 8} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 8, 14} ∨
        polygon = {1, 4, 7, 8, 14} ∨
        polygon = {1, 4, 6, 8, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 8} ∨
        polygon = {1, 3, 7, 8, 14} ∨
        polygon = {1, 3, 6, 8, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 8} ∨
        polygon = {1, 3, 4, 8, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 8} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 8} ∨
        polygon = {1, 3, 4, 6, 7} ∨
        polygon = {1, 2, 7, 8, 14} ∨
        polygon = {1, 2, 6, 8, 14} ∨
        polygon = {1, 2, 6, 7, 14} ∨
        polygon = {1, 2, 6, 7, 8} ∨
        polygon = {1, 2, 4, 8, 14} ∨
        polygon = {1, 2, 4, 7, 14} ∨
        polygon = {1, 2, 4, 7, 8} ∨
        polygon = {1, 2, 4, 6, 14} ∨
        polygon = {1, 2, 4, 6, 8} ∨
        polygon = {1, 2, 4, 6, 7} ∨
        polygon = {1, 2, 3, 8, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 8} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 8} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 8} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask16862] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask01758 :
    (({1, 2, 3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {3, 6, 7, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 6, 7, 10}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 4, 6, 9, 10}, {2, 4, 6, 7, 10}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 6, 7, 10}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {1, 6, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {1, 2, 7, 9, 10}, {1, 2, 6, 9, 10}, {1, 2, 6, 7, 10}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 10}, {1, 2, 4, 7, 10}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 3, 9, 10}, {1, 2, 3, 7, 10}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask01758 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 9, 10} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 10} ∨
        polygon = {3, 6, 7, 9, 10} ∨
        polygon = {3, 4, 7, 9, 10} ∨
        polygon = {3, 4, 6, 9, 10} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 10} ∨
        polygon = {2, 4, 7, 9, 10} ∨
        polygon = {2, 4, 6, 9, 10} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 10} ∨
        polygon = {2, 3, 6, 9, 10} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 10} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 9, 10} ∨
        polygon = {1, 4, 7, 9, 10} ∨
        polygon = {1, 4, 6, 9, 10} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 10} ∨
        polygon = {1, 3, 6, 9, 10} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 10} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {1, 2, 3, 9, 10} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask01758] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask04830 :
    (({1, 2, 3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {3, 6, 7, 9, 12}, {3, 4, 7, 9, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 4, 6, 9, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {1, 6, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {1, 2, 7, 9, 12}, {1, 2, 6, 9, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 3, 9, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask04830 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 9, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 12} ∨
        polygon = {3, 6, 7, 9, 12} ∨
        polygon = {3, 4, 7, 9, 12} ∨
        polygon = {3, 4, 6, 9, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 12} ∨
        polygon = {2, 4, 7, 9, 12} ∨
        polygon = {2, 4, 6, 9, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 12} ∨
        polygon = {2, 3, 6, 9, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 9, 12} ∨
        polygon = {1, 4, 7, 9, 12} ∨
        polygon = {1, 4, 6, 9, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 12} ∨
        polygon = {1, 3, 6, 9, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {1, 2, 3, 9, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask04830] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask08926 :
    (({1, 2, 3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {3, 6, 7, 9, 13}, {3, 4, 7, 9, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 4, 6, 9, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {1, 6, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {1, 2, 7, 9, 13}, {1, 2, 6, 9, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 3, 9, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask08926 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 9, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 13} ∨
        polygon = {3, 6, 7, 9, 13} ∨
        polygon = {3, 4, 7, 9, 13} ∨
        polygon = {3, 4, 6, 9, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 13} ∨
        polygon = {2, 4, 7, 9, 13} ∨
        polygon = {2, 4, 6, 9, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 13} ∨
        polygon = {2, 3, 6, 9, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 9, 13} ∨
        polygon = {1, 4, 7, 9, 13} ∨
        polygon = {1, 4, 6, 9, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 13} ∨
        polygon = {1, 3, 6, 9, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {1, 2, 3, 9, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask08926] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17118 :
    (({1, 2, 3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {3, 6, 7, 9, 14}, {3, 4, 7, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 9}, {2, 6, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 4, 6, 9, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 9}, {2, 3, 7, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 9}, {2, 3, 4, 9, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}, {1, 6, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 9}, {1, 3, 7, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 9}, {1, 3, 4, 9, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}, {1, 2, 7, 9, 14}, {1, 2, 6, 9, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 9}, {1, 2, 4, 9, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 9}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 9}, {1, 2, 4, 6, 7}, {1, 2, 3, 9, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 9}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 9}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 9}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17118 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 9, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 9, 14} ∨
        polygon = {3, 6, 7, 9, 14} ∨
        polygon = {3, 4, 7, 9, 14} ∨
        polygon = {3, 4, 6, 9, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 9} ∨
        polygon = {2, 6, 7, 9, 14} ∨
        polygon = {2, 4, 7, 9, 14} ∨
        polygon = {2, 4, 6, 9, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 9} ∨
        polygon = {2, 3, 7, 9, 14} ∨
        polygon = {2, 3, 6, 9, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 9} ∨
        polygon = {2, 3, 4, 9, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 9} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 9} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 9, 14} ∨
        polygon = {1, 4, 7, 9, 14} ∨
        polygon = {1, 4, 6, 9, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 9} ∨
        polygon = {1, 3, 7, 9, 14} ∨
        polygon = {1, 3, 6, 9, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 9} ∨
        polygon = {1, 3, 4, 9, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 9} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 9} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {1, 2, 3, 9, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 9} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 9} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 9} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17118] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask05342 :
    (({1, 2, 3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {3, 6, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}, {2, 6, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 4, 6, 10, 12}, {2, 4, 6, 7, 12}, {2, 4, 6, 7, 10}, {2, 3, 7, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 6, 7, 12}, {2, 3, 6, 7, 10}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {1, 6, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}, {1, 3, 7, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {1, 2, 7, 10, 12}, {1, 2, 6, 10, 12}, {1, 2, 6, 7, 12}, {1, 2, 6, 7, 10}, {1, 2, 4, 10, 12}, {1, 2, 4, 7, 12}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 12}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 3, 10, 12}, {1, 2, 3, 7, 12}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 12}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 12}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask05342 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 10, 12} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 12} ∨
        polygon = {3, 6, 7, 10, 12} ∨
        polygon = {3, 4, 7, 10, 12} ∨
        polygon = {3, 4, 6, 10, 12} ∨
        polygon = {3, 4, 6, 7, 12} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 12} ∨
        polygon = {2, 4, 7, 10, 12} ∨
        polygon = {2, 4, 6, 10, 12} ∨
        polygon = {2, 4, 6, 7, 12} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 12} ∨
        polygon = {2, 3, 6, 10, 12} ∨
        polygon = {2, 3, 6, 7, 12} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 4, 10, 12} ∨
        polygon = {2, 3, 4, 7, 12} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 12} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 10, 12} ∨
        polygon = {1, 4, 7, 10, 12} ∨
        polygon = {1, 4, 6, 10, 12} ∨
        polygon = {1, 4, 6, 7, 12} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 12} ∨
        polygon = {1, 3, 6, 10, 12} ∨
        polygon = {1, 3, 6, 7, 12} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 10, 12} ∨
        polygon = {1, 3, 4, 7, 12} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 12} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {1, 2, 3, 10, 12} ∨
        polygon = {1, 2, 3, 7, 12} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 12} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 12} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask05342] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask09438 :
    (({1, 2, 3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {3, 6, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}, {2, 6, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 4, 6, 10, 13}, {2, 4, 6, 7, 13}, {2, 4, 6, 7, 10}, {2, 3, 7, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 6, 7, 13}, {2, 3, 6, 7, 10}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {1, 6, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}, {1, 3, 7, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {1, 2, 7, 10, 13}, {1, 2, 6, 10, 13}, {1, 2, 6, 7, 13}, {1, 2, 6, 7, 10}, {1, 2, 4, 10, 13}, {1, 2, 4, 7, 13}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 13}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 3, 10, 13}, {1, 2, 3, 7, 13}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 13}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 13}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask09438 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 10, 13} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 13} ∨
        polygon = {3, 6, 7, 10, 13} ∨
        polygon = {3, 4, 7, 10, 13} ∨
        polygon = {3, 4, 6, 10, 13} ∨
        polygon = {3, 4, 6, 7, 13} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 13} ∨
        polygon = {2, 4, 7, 10, 13} ∨
        polygon = {2, 4, 6, 10, 13} ∨
        polygon = {2, 4, 6, 7, 13} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 13} ∨
        polygon = {2, 3, 6, 10, 13} ∨
        polygon = {2, 3, 6, 7, 13} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 4, 10, 13} ∨
        polygon = {2, 3, 4, 7, 13} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 13} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 10, 13} ∨
        polygon = {1, 4, 7, 10, 13} ∨
        polygon = {1, 4, 6, 10, 13} ∨
        polygon = {1, 4, 6, 7, 13} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 13} ∨
        polygon = {1, 3, 6, 10, 13} ∨
        polygon = {1, 3, 6, 7, 13} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 10, 13} ∨
        polygon = {1, 3, 4, 7, 13} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 13} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {1, 2, 3, 10, 13} ∨
        polygon = {1, 2, 3, 7, 13} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 13} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 13} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask09438] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

theorem fin15Anchored_fiveFamily_mask17630 :
    (({1, 2, 3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {3, 6, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}, {2, 6, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 4, 6, 10, 14}, {2, 4, 6, 7, 14}, {2, 4, 6, 7, 10}, {2, 3, 7, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 6, 7, 14}, {2, 3, 6, 7, 10}, {2, 3, 4, 10, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}, {1, 6, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}, {1, 3, 7, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}, {1, 3, 4, 10, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}, {1, 2, 7, 10, 14}, {1, 2, 6, 10, 14}, {1, 2, 6, 7, 14}, {1, 2, 6, 7, 10}, {1, 2, 4, 10, 14}, {1, 2, 4, 7, 14}, {1, 2, 4, 7, 10}, {1, 2, 4, 6, 14}, {1, 2, 4, 6, 10}, {1, 2, 4, 6, 7}, {1, 2, 3, 10, 14}, {1, 2, 3, 7, 14}, {1, 2, 3, 7, 10}, {1, 2, 3, 6, 14}, {1, 2, 3, 6, 10}, {1, 2, 3, 6, 7}, {1, 2, 3, 4, 14}, {1, 2, 3, 4, 10}, {1, 2, 3, 4, 7}, {1, 2, 3, 4, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl

theorem fin15Anchored_fiveSubset_mask17630 :
    ∀ polygon : Finset (Fin 15), polygon ⊆ {1, 2, 3, 4, 6, 7, 10, 14} →
      polygon.card = 5 →
        polygon = {4, 6, 7, 10, 14} ∨
        polygon = {3, 6, 7, 10, 14} ∨
        polygon = {3, 4, 7, 10, 14} ∨
        polygon = {3, 4, 6, 10, 14} ∨
        polygon = {3, 4, 6, 7, 14} ∨
        polygon = {3, 4, 6, 7, 10} ∨
        polygon = {2, 6, 7, 10, 14} ∨
        polygon = {2, 4, 7, 10, 14} ∨
        polygon = {2, 4, 6, 10, 14} ∨
        polygon = {2, 4, 6, 7, 14} ∨
        polygon = {2, 4, 6, 7, 10} ∨
        polygon = {2, 3, 7, 10, 14} ∨
        polygon = {2, 3, 6, 10, 14} ∨
        polygon = {2, 3, 6, 7, 14} ∨
        polygon = {2, 3, 6, 7, 10} ∨
        polygon = {2, 3, 4, 10, 14} ∨
        polygon = {2, 3, 4, 7, 14} ∨
        polygon = {2, 3, 4, 7, 10} ∨
        polygon = {2, 3, 4, 6, 14} ∨
        polygon = {2, 3, 4, 6, 10} ∨
        polygon = {2, 3, 4, 6, 7} ∨
        polygon = {1, 6, 7, 10, 14} ∨
        polygon = {1, 4, 7, 10, 14} ∨
        polygon = {1, 4, 6, 10, 14} ∨
        polygon = {1, 4, 6, 7, 14} ∨
        polygon = {1, 4, 6, 7, 10} ∨
        polygon = {1, 3, 7, 10, 14} ∨
        polygon = {1, 3, 6, 10, 14} ∨
        polygon = {1, 3, 6, 7, 14} ∨
        polygon = {1, 3, 6, 7, 10} ∨
        polygon = {1, 3, 4, 10, 14} ∨
        polygon = {1, 3, 4, 7, 14} ∨
        polygon = {1, 3, 4, 7, 10} ∨
        polygon = {1, 3, 4, 6, 14} ∨
        polygon = {1, 3, 4, 6, 10} ∨
        polygon = {1, 3, 4, 6, 7} ∨
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
        polygon = {1, 2, 3, 10, 14} ∨
        polygon = {1, 2, 3, 7, 14} ∨
        polygon = {1, 2, 3, 7, 10} ∨
        polygon = {1, 2, 3, 6, 14} ∨
        polygon = {1, 2, 3, 6, 10} ∨
        polygon = {1, 2, 3, 6, 7} ∨
        polygon = {1, 2, 3, 4, 14} ∨
        polygon = {1, 2, 3, 4, 10} ∨
        polygon = {1, 2, 3, 4, 7} ∨
        polygon = {1, 2, 3, 4, 6} := by
  intro polygon hsubset hcard
  have hmem : polygon ∈ (({1, 2, 3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩)
  rw [fin15Anchored_fiveFamily_mask17630] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  exact hmem

end ErdosSzekeres

end
